"""本地彩票历史数据分析与随机选号网页（仅标准库，无第三方依赖）。"""
from __future__ import annotations

import csv
import datetime as dt
import html
import io
import json
import math
import random
import re
import threading
import time
import urllib.parse
import urllib.request
import uuid
import zipfile
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from xml.etree import ElementTree as ET

ROOT = Path(__file__).resolve().parent
DATA_FILE = ROOT / "draws.json"
TICKETS_FILE = ROOT / "tickets.json"
LOCK = threading.Lock()
SYNC_LOCK = threading.Lock()
AUTO_STATUS_LOCK = threading.Lock()
AUTO_SCHEDULE = {
    "ssq": ({1, 3, 6}, (21, 15)),
    "dlt": ({0, 2, 5}, (21, 25)),
    "3d": (set(range(7)), (21, 15)),
    "pls": (set(range(7)), (21, 25)),
    "kl8": (set(range(7)), (21, 30)),
}
AUTO_ATTEMPTS = {}
AUTO_DONE = set()
GAMES = {
    "ssq": {"name": "双色球", "groups": [("红球", 33, 6, True), ("蓝球", 16, 1, False)], "url": "https://www.zhcw.com/kjxx/ssq/"},
    "dlt": {"name": "超级大乐透", "groups": [("前区", 35, 5, True), ("后区", 12, 2, True)], "url": "https://www.lottery.gov.cn/kj/kjlb.html?dlt"},
    "3d": {"name": "福彩3D", "groups": [("号码", 10, 3, False)], "url": "https://www.zhcw.com/kjxx/3d/"},
    "pls": {"name": "排列3", "groups": [("号码", 10, 3, False)], "url": "https://www.lottery.gov.cn/kj/kjlb.html?pls"},
    "kl8": {"name": "快乐8", "groups": [("号码", 80, 20, True)], "url": "https://www.zhcw.com/kjxx/kl8/"},
}
AUTO_STATUS = {"_all": {"state": "等待启动", "progress": 0, "detail": "准备启动后台同步"}}
AUTO_STATUS.update({game: {"state": "等待启动", "progress": 0, "detail": "", "updated_at": None, "error": None} for game in GAMES})

def load_data():
    try:
        data = json.loads(DATA_FILE.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except (OSError, json.JSONDecodeError):
        return {}

def save_data(data):
    DATA_FILE.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

def load_tickets():
    try:
        value=json.loads(TICKETS_FILE.read_text(encoding="utf-8"))
        return value if isinstance(value,list) else []
    except (OSError,json.JSONDecodeError):
        return []

def save_tickets(tickets):
    TICKETS_FILE.write_text(json.dumps(tickets,ensure_ascii=False,indent=2),encoding="utf-8")

def settle_tickets(game, rows):
    """将待核对号码绑定到其生成基准期之后的第一期开奖。"""
    tickets=load_tickets()
    if not rows:return tickets
    latest=max((int(r["period"]) for r in rows),default=0)
    changed=False
    for ticket in tickets:
        if ticket.get("game")!=game:continue
        if ticket.get("status")=="已结算":
            if not ticket.get("draw_date"):
                matching=next((r for r in rows if str(r.get("period"))==str(ticket.get("draw_period"))),None)
                if matching and matching.get("date"):
                    ticket["draw_date"]=matching["date"]; changed=True
            continue
        if ticket.get("base_period") is None:
            ticket["base_period"]=latest; changed=True; continue
        candidates=[r for r in rows if int(r["period"])>int(ticket["base_period"])]
        if not candidates:continue
        draw=min(candidates,key=lambda r:int(r["period"]))
        ticket.update(score_ticket(game,ticket["numbers"],draw))
        ticket["status"]="已结算"; ticket["draw_period"]=draw["period"]; ticket["draw_numbers"]=draw["numbers"]; ticket["draw_date"]=draw.get("date")
        changed=True
    if changed:save_tickets(tickets)
    return tickets

def _award_value(draw, tier):
    awards=draw.get("awards") or {}
    raw=awards.get(str(tier))
    try:return float(str(raw).replace(",", "")) if raw not in (None, "") else None
    except (TypeError,ValueError):return None

def score_ticket(game, ticket, draw):
    groups=GAMES[game]["groups"]
    def group_hits():
        values=[];offset=0
        for _,_,amount,_ in groups:
            values.append(sum(a==b for a,b in zip(ticket[offset:offset+amount],draw["numbers"][offset:offset+amount])))
            offset+=amount
        return values
    if game=="ssq":
        r=sum(a==b for a,b in zip(ticket[:6],draw["numbers"][:6])); blue=ticket[6]==draw["numbers"][6]
        tier=1 if r==6 and blue else 2 if r==6 else 3 if r==5 and blue else 4 if r==5 or (r==4 and blue) else 5 if r==4 or (r==3 and blue) else 6 if blue else 0
        fixed={3:3000,4:200,5:10,6:5}
    elif game=="dlt":
        f=sum(a==b for a,b in zip(ticket[:5],draw["numbers"][:5])); b=sum(a==b for a,b in zip(ticket[5:],draw["numbers"][5:]))
        tier=1 if (f,b)==(5,2) else 2 if (f,b)==(5,1) else 3 if (f,b) in ((5,0),(4,2)) else 4 if (f,b)==(4,1) else 5 if (f,b) in ((4,0),(3,2)) else 6 if (f,b) in ((3,1),(2,2)) else 7 if (f,b) in ((3,0),(2,1),(1,2),(0,2)) else 0
        fixed={}
    elif game in ("3d","pls"):
        win=ticket==draw["numbers"]; tier=1 if win else 0; fixed={1:1040}
    else:
        hits=sum(n in draw["numbers"] for n in ticket)
        k=len(ticket)
        tables={1:{1:4.5},2:{2:19},3:{3:52,2:3},4:{4:93,3:5,2:3},5:{5:1000,4:20,3:3},6:{6:2880,5:30,4:10,3:3},7:{7:8500,6:300,5:30,4:4,0:2},8:{8:50000,7:800,6:80,5:10,4:3},9:{8:2000,7:225,6:22,5:5,4:3},10:{8:720,7:80,6:5,5:3,0:2}}
        variable=(k==9 and hits==9) or (k==10 and hits==10)
        prize=None if variable else tables.get(k,{}).get(hits,0)
        note="选九中九、选十中十为浮动奖，需以本期开奖公告为准" if variable else ""
        return {"hits": [hits], "tier": f"选{k}中{hits}" if hits else f"选{k}全不中", "prize": prize, "prize_note": note}
    if not tier:return {"hits":group_hits(),"tier":"未中奖","prize":0,"prize_note":""}
    amount=_award_value(draw,tier)
    if amount is None:amount=fixed.get(tier)
    note="" if amount is not None else "本期奖级奖金数据未随开奖结果提供，已记录命中奖级"
    return {"hits":group_hits(),"tier":f"{tier}等奖","prize":amount,"prize_note":note}

def extract_awards(item, game):
    awards={}
    for prize in item.get("prizegrades",[]) or []:
        if prize.get("type") is not None:awards[str(prize["type"])]=prize.get("typemoney")
    labels={"一等奖":"1","二等奖":"2","三等奖":"3","四等奖":"4","五等奖":"5","六等奖":"6","七等奖":"7","八等奖":"8","九等奖":"9"}
    for prize in item.get("prizeLevelList",[]) or []:
        raw_tier=str(prize.get("prizeLevel",""))
        tier=labels.get(raw_tier,raw_tier if raw_tier.isdigit() else None)
        amount=next((prize.get(k) for k in ("stakeAmount","singleBonus","typemoney","prizeMoney") if prize.get(k) not in (None,"")),None)
        if tier and amount is not None:awards[tier]=amount
    return awards

def parse_rows(text, game):
    """接受 CSV：期号,号码1,...；也接受 XLSX 首个工作表。"""
    rows = []
    if text[:2] == "PK":
        raise ValueError("内部错误：XLSX 请使用 parse_xlsx")
    for row in csv.reader(io.StringIO(text.lstrip("\ufeff"))):
        row = [x.strip() for x in row]
        if len(row) < 2 or not row[0]:
            continue
        try:
            period = row[0]
            nums = [int(re.sub(r"\D", "", x)) for x in row[1:] if re.search(r"\d", x)]
            if not period.isdigit():
                continue  # 标题行
            if game == "ssq" and len(nums) >= 7:
                nums = nums[:7]
            elif game == "dlt" and len(nums) >= 7:
                nums = nums[:7]
            elif game == "kl8" and len(nums) >= 20:
                nums = nums[:20]
            elif game in ("3d", "pls") and len(nums) >= 3:
                nums = nums[:3]
            else:
                continue
            groups = GAMES[game]["groups"]
            offset = 0
            valid = True
            for _, maximum, count, sorted_group in groups:
                chunk = nums[offset:offset + count]
                if len(chunk) != count or any(n < 1 or n > maximum for n in chunk):
                    valid = False
                if sorted_group and len(set(chunk)) != count:
                    valid = False
                offset += count
            if valid:
                rows.append({"period": period, "numbers": nums})
        except (ValueError, IndexError):
            continue
    return rows

def parse_xlsx(raw, game):
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        shared = []
        if "xl/sharedStrings.xml" in z.namelist():
            root = ET.fromstring(z.read("xl/sharedStrings.xml"))
            shared = ["".join(t.text or "" for t in si.iter() if t.tag.endswith("}t")) for si in root]
        sheet = next(n for n in z.namelist() if re.fullmatch(r"xl/worksheets/sheet\d+\.xml", n))
        root = ET.fromstring(z.read(sheet))
        table = []
        for row in root.iter():
            if not row.tag.endswith("}row"):
                continue
            vals = []
            for cell in row:
                if not cell.tag.endswith("}c"):
                    continue
                v = next((x.text for x in cell if x.tag.endswith("}v")), "")
                if cell.attrib.get("t") == "s" and v:
                    v = shared[int(v)]
                vals.append(v)
            table.append(vals)
    return parse_rows("\n".join(",".join(r) for r in table), game)

def entropy(probabilities):
    return -sum(p * math.log2(p) for p in probabilities if p > 0)

def analyze(game, rows):
    groups = GAMES[game]["groups"]
    report = []
    for gi, (label, maximum, count, _) in enumerate(groups):
        positional = game in ("3d", "pls")
        positions = count if positional else 1
        for pos in range(positions):
            hits = [0] * maximum
            for row in rows:
                values = row["numbers"]
                if positional:
                    hits[values[pos] - 1] += 1
                else:
                    for n in values[sum(g[2] for g in groups[:gi]):sum(g[2] for g in groups[:gi+1])]:
                        hits[n - 1] += 1
            total = sum(hits)
            probs = [n / total for n in hits] if total else [1 / maximum] * maximum
            name = ["百位", "十位", "个位"][pos] if positional else label
            report.append({"label": name, "hits": hits, "entropy": entropy(probs), "maxEntropy": math.log2(maximum), "coverage": total})
    return report

def posterior_weights(game, rows, prior_strength=20):
    """Dirichlet 对称先验：P(n|D)=(count(n)+alpha/K)/(N+alpha)。"""
    result = []
    groups = GAMES[game]["groups"]
    for gi, (_, maximum, _, _) in enumerate(groups):
        positions = 3 if game in ("3d", "pls") else 1
        lo = sum(g[2] for g in groups[:gi]); hi = lo + groups[gi][2]
        group_weights = []
        for pos in range(positions):
            hits = [0] * maximum
            for row in rows:
                selected = [row["numbers"][pos]] if positions > 1 else row["numbers"][lo:hi]
                for n in selected: hits[n - 1] += 1
            total = sum(hits)
            group_weights.append([(x + prior_strength / maximum) / (total + prior_strength) for x in hits])
        result.append(group_weights)
    return result

def generate(game, rows, count=5, temperature=1.0, exclusions=None, selection_count=10):
    weights = posterior_weights(game, rows)
    exclusions = exclusions or [[] for _ in GAMES[game]["groups"]]
    out = []
    for _ in range(count):
        ticket = []
        for gi, (_, maximum, amount, sorted_group) in enumerate(GAMES[game]["groups"]):
            if game=="kl8":amount=selection_count
            w = [p ** (1 / temperature) for p in weights[gi][0]]
            excluded = set(exclusions[gi])
            pool = [n for n in range(1, maximum + 1) if n not in excluded]
            if len(pool) < amount:
                raise ValueError(f"排除号码过多：该区至少需要保留 {amount} 个可选号码")
            if game in ("3d", "pls"):
                values = [random.choices(pool, weights=[weights[gi][pos][n - 1] ** (1 / temperature) for n in pool], k=1)[0] for pos in range(amount)]
            elif sorted_group:
                values = []
                for _ in range(amount):
                    chosen = random.choices(pool, weights=[w[n - 1] for n in pool], k=1)[0]
                    values.append(chosen); pool.remove(chosen)
                values.sort()
            else:
                values = random.choices(pool, weights=[w[n - 1] for n in pool], k=amount)
            ticket.extend(values)
        out.append(ticket)
    return out

def fetch_cwl(game, limit=None, on_progress=None):
    """从中国福利彩票中心公开接口分页读取历史开奖数据。"""
    landing = {"ssq": "https://www.cwl.gov.cn/ygkj/wqkjgg/ssq/", "3d": "https://www.cwl.gov.cn/ygkj/wqkjgg/fc3d/", "kl8": "https://www.cwl.gov.cn/ygkj/wqkjgg/kl8/"}[game]
    opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor())
    opener.open(urllib.request.Request(landing, headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/124.0 Safari/537.36"}), timeout=25).close()
    result = []
    for page in range(1, 101):
        query = urllib.parse.urlencode({"name": game, "issueCount": "", "issueStart": "", "issueEnd": "", "dayStart": "", "dayEnd": "", "pageNo": page, "pageSize": min(100, limit) if limit else 100, "systemType": "PC"})
        req = urllib.request.Request("https://www.cwl.gov.cn/cwl_admin/front/cwlkj/search/kjxx/findDrawNotice?" + query, headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/124.0 Safari/537.36", "Accept": "application/json", "Referer": landing})
        with opener.open(req, timeout=25) as response:
            payload = json.loads(response.read().decode("utf-8-sig"))
        items = payload.get("result") or []
        if not items: break
        for item in items:
            period = str(item.get("code", "")); raw = str(item.get("red", ""))
            if game == "ssq": raw += "," + str(item.get("blue", ""))
            nums = [int(n) for n in re.findall(r"\d+", raw)]
            if period.isdigit() and len(nums) == sum(g[2] for g in GAMES[game]["groups"]):
                date_match=re.search(r"\d{4}-\d{2}-\d{2}",str(item.get("date", "")))
                result.append({"period": period, "numbers": nums, "date": date_match.group(0) if date_match else None, "awards": extract_awards(item,game)})
                if limit and len(result)>=limit:break
        if on_progress:on_progress(page,len(result))
        if limit and len(result)>=limit:break
        if len(items) < 100: break
        time.sleep(.12)
    if not result: raise ValueError("福彩官方接口没有返回记录，请稍后重试")
    return result

def fetch_sporttery(game, limit=None, on_progress=None):
    """从中国体彩网公开历史开奖接口读取大乐透或排列3。"""
    game_no = {"dlt": "85", "pls": "35"}[game]; result = []
    headers = {"User-Agent": "Mozilla/5.0 (Linux; Android 14) AppleWebKit/537.36 Chrome/120.0.0.0 Mobile Safari/537.36", "Accept": "application/json", "Referer": "https://m.lottery.gov.cn/"}
    for page in range(1, 101):
        query = urllib.parse.urlencode({"gameNo": game_no, "provinceId": "0", "pageSize": min(100, limit) if limit else 100, "isVerify": 1, "pageNo": page})
        req = urllib.request.Request("https://webapi.sporttery.cn/gateway/lottery/getHistoryPageListV1.qry?" + query, headers=headers)
        with urllib.request.urlopen(req, timeout=25) as response:
            payload = json.loads(response.read().decode("utf-8-sig"))
        items = (payload.get("value") or {}).get("list") or []
        if not items: break
        for item in items:
            period = str(item.get("lotteryDrawNum", ""))
            nums = [int(n) for n in re.findall(r"\d+", str(item.get("lotteryDrawResult", "")))]
            if period.isdigit() and len(nums) == sum(g[2] for g in GAMES[game]["groups"]):
                date_match=re.search(r"\d{4}-\d{2}-\d{2}",str(item.get("lotteryDrawTime", "")))
                result.append({"period": period, "numbers": nums, "date": date_match.group(0) if date_match else None, "awards": extract_awards(item,game)})
                if limit and len(result)>=limit:break
        if on_progress:on_progress(page,len(result))
        if limit and len(result)>=limit:break
        if len(items) < 100: break
        time.sleep(.12)
    if not result: raise ValueError("体彩官方接口没有返回记录，请稍后重试")
    return result

def fetch_history(game, limit=None, on_progress=None):
    return fetch_cwl(game, limit, on_progress) if game in ("ssq", "3d", "kl8") else fetch_sporttery(game, limit, on_progress)

def sync_game(game, initial=False, full=False, overall=None):
    """首次缺少本地历史时完整下载，其余时间拉取最近开奖并合并。"""
    with SYNC_LOCK:
        with AUTO_STATUS_LOCK:
            AUTO_STATUS[game].update(state="正在同步", progress=0, detail="连接官方开奖数据", error=None)
            if not overall:AUTO_STATUS["_all"].update(state="正在更新"+GAMES[game]["name"], progress=0, detail="连接官方开奖数据")
        try:
            local=load_data().get(game, [])
            limit=None if full or (initial and not local) else 10
            def report(page,found):
                local_progress=min(90,page) if limit is None else 85
                detail=("历史第 %s 页，已读取 %s 期"%(page,found)) if limit is None else ("正在核对最近记录，已读取 %s 期"%found)
                with AUTO_STATUS_LOCK:
                    AUTO_STATUS[game].update(progress=local_progress,detail=detail)
                    if overall:
                        index,total=overall
                        AUTO_STATUS["_all"].update(progress=min(99,int((index+local_progress/100)/total*100)),detail=GAMES[game]["name"]+"："+detail)
                    else:AUTO_STATUS["_all"].update(progress=local_progress,detail=GAMES[game]["name"]+"："+detail)
            rows=fetch_history(game, limit, report)
            with LOCK:
                data=load_data(); old={str(r["period"]):r for r in data.get(game,[])}; before=len(old)
                old.update({str(r["period"]):r for r in rows}); data[game]=list(old.values()); save_data(data)
                settle_tickets(game,list(old.values()))
            with AUTO_STATUS_LOCK:
                AUTO_STATUS[game].update(state="已同步", progress=100, detail="共 %s 期"%len(rows), updated_at=dt.datetime.now().astimezone().isoformat(timespec="minutes"), error=None)
                if overall:
                    index,total=overall
                    AUTO_STATUS["_all"].update(progress=min(99,int((index+1)/total*100)),detail=GAMES[game]["name"]+"同步完成")
                else:AUTO_STATUS["_all"].update(progress=100,detail=GAMES[game]["name"]+"同步完成")
            return {"added":len(old)-before,"total":len(old),"rows":rows}
        except Exception as exc:
            with AUTO_STATUS_LOCK:
                AUTO_STATUS[game].update(state="同步失败", detail="可检查网络或稍后重试", error=str(exc))
                if overall:
                    index,total=overall
                    AUTO_STATUS["_all"].update(progress=min(99,int((index+1)/total*100)),detail=GAMES[game]["name"]+"同步失败，将继续其余品种")
                else:AUTO_STATUS["_all"].update(state="更新失败",detail=GAMES[game]["name"]+"同步失败")
            raise

def auto_update_loop():
    """开机补齐所有品种；开奖日之后每 15 分钟重试，最多约 90 分钟。"""
    def startup_sync():
        with AUTO_STATUS_LOCK:AUTO_STATUS["_all"].update(state="启动同步中",progress=0,detail="准备同步全部品种")
        failures=[];total=len(GAMES)
        for index,game in enumerate(GAMES):
            try:sync_game(game, initial=True, overall=(index,total))
            except Exception:failures.append(GAMES[game]["name"])
        with AUTO_STATUS_LOCK:
            AUTO_STATUS["_all"].update(state="启动同步完成" if not failures else "启动同步完成（部分失败）",progress=100,detail="全部品种检查完毕" if not failures else "失败："+"、".join(failures))
    threading.Thread(target=startup_sync, name="lottery-startup-sync", daemon=True).start()
    while True:
        now=dt.datetime.now().astimezone(); today=now.date().isoformat()
        for game,(weekdays,(hour,minute)) in AUTO_SCHEDULE.items():
            if now.weekday() not in weekdays:continue
            due=now.replace(hour=hour,minute=minute,second=0,microsecond=0)+dt.timedelta(minutes=5)
            slot=game+":"+today
            if now<due or now>due+dt.timedelta(minutes=95) or slot in AUTO_DONE:continue
            attempts=AUTO_ATTEMPTS.get(slot,0)
            if attempts>=7 or now.minute%15 not in (0,1,2):continue
            AUTO_ATTEMPTS[slot]=attempts+1
            try:
                result=sync_game(game)
                if any(row.get("date")==today for row in result["rows"]):AUTO_DONE.add(slot)
            except Exception:pass
        time.sleep(60)

PAGE = r'''<!doctype html><html lang="zh"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>彩票数据实验室</title>
<style>
:root{color-scheme:dark;--bg:#10131b;--panel:#191e2b;--line:#2c3445;--ink:#edf1fa;--muted:#9ca8bc;--a:#a7f3d0;--b:#818cf8}*{box-sizing:border-box}body{margin:0;background:radial-gradient(ellipse at 20% 0,#233451 0,transparent 42%),var(--bg);color:var(--ink);font:15px/1.55 system-ui,"Microsoft YaHei",sans-serif}main{max-width:1050px;margin:auto;padding:34px 20px 70px}header{display:flex;align-items:end;justify-content:space-between;gap:18px;margin:14px 0 26px}h1{font-size:32px;letter-spacing:-1px;margin:0}h2{font-size:18px;margin:0 0 14px}.sub,.muted{color:var(--muted)}.grid{display:grid;grid-template-columns:1fr 1fr;gap:16px}.card{background:linear-gradient(145deg,#1d2432,#171b26);border:1px solid var(--line);border-radius:16px;padding:20px;box-shadow:0 10px 30px #0002}.wide{grid-column:1/-1}select,button,input[type=file],textarea{font:inherit;color:var(--ink);background:#10141e;border:1px solid #3a455a;border-radius:10px;padding:11px}select{min-width:175px}textarea{width:100%;height:110px;resize:vertical}button{background:#a7f3d0;color:#10231b;font-weight:700;border:0;cursor:pointer;padding:11px 16px}button.secondary{background:#30394b;color:var(--ink);border:1px solid #46516a}label{display:block;margin:8px 0;color:var(--muted)}.row{display:flex;flex-wrap:wrap;align-items:center;gap:10px}.stats{display:flex;gap:14px;flex-wrap:wrap}.stat{flex:1;min-width:140px;background:#111621;border:1px solid var(--line);padding:14px;border-radius:12px}.stat b{display:block;font-size:23px}.barrow{display:flex;align-items:center;gap:8px;margin:5px 0;font-variant-numeric:tabular-nums}.barrow .n{width:30px;text-align:right;color:var(--muted)}.track{height:8px;background:#2a3140;flex:1;border-radius:8px;overflow:hidden}.fill{height:100%;background:linear-gradient(90deg,var(--b),var(--a));border-radius:8px}.ball{display:inline-flex;width:38px;height:38px;border-radius:50%;align-items:center;justify-content:center;margin:3px;background:#26344b;border:1px solid #536c91;font-weight:700}.ball.red{background:#492c3c;border-color:#a54b69}.ticket{padding:12px 0;border-bottom:1px solid var(--line)}.warn{border-left:3px solid #fbbf24;padding:10px 13px;background:#2a2417;border-radius:5px;color:#f5daa0}.ok{color:var(--a)}.error{color:#fda4af}.hidden{display:none}.progress{height:12px;background:#2a3140;border-radius:99px;overflow:hidden;margin:10px 0}.progress>div{height:100%;width:0;background:linear-gradient(90deg,var(--b),var(--a));transition:width .4s}a{color:#a7f3d0}@media(max-width:700px){.grid{grid-template-columns:1fr}.wide{grid-column:auto}header{align-items:start;flex-direction:column}}
</style><main><header><div><h1>开奖数据实验室</h1><div class="sub">历史频率 · 贝叶斯平滑 · 香农熵 · 随机选号</div></div><select id="game"></select></header>
<div class="warn">开奖在公平机制下相互独立。历史数据的频率与熵只描述过去，不能提高下一期开奖的中奖概率；生成号码仅供学习与娱乐，请理性购彩。</div>
<section class="grid" style="margin-top:16px"><article class="card"><h2>历史数据</h2><div class="stats"><div class="stat"><span class="muted">已导入期数</span><b id="total">0</b></div><div class="stat"><span class="muted">最近一期</span><b id="latest">—</b></div></div><button id="download">自动下载/更新开奖数据</button><div class="progress"><div id="autoProgressBar"></div></div><p id="autoProgressText" class="muted">总体进度：0% · 准备启动</p><p id="autoStatus" class="muted">自动更新启动中…</p><label>导入 CSV / Excel（首个工作表，列为“期号、号码1、号码2…”）</label><input id="file" type="file" accept=".csv,.xlsx"><button id="upload" class="secondary">导入文件</button><label>或粘贴 CSV 内容</label><textarea id="paste" placeholder="期号,号码1,号码2,...&#10;2025001,01,02,..."></textarea><button id="importText" class="secondary">导入粘贴内容</button><p id="msg" class="muted"></p><p class="muted">官方下载页：<a id="official" target="_blank" rel="noopener">打开当前彩种</a></p></article>
<article class="card"><h2>贝叶斯号码建议</h2><p class="muted">对每个号码采用对称 Dirichlet 先验 α=20，后验概率为 (出现次数 + α/K) / (总次数 + α)。</p><label><input id="excludePrevious" type="checkbox" checked> 排除最近一期开奖号码</label><div id="excludeControls"></div><div class="row"><label>生成注数 <select id="amount"><option>5</option><option>1</option><option>10</option><option>20</option></select></label><button id="generate">生成参考号码</button></div><div id="tickets"></div></article>
<article class="card wide"><h2>已保存号码与开奖核对</h2><p class="muted">每次生成会自动保存，并等待生成基准期之后的下一期结果。默认查看最近一期；也可查总览、期号或日期。下载或导入新开奖后自动结算。奖金为一注2元单式投注的模拟税前金额，不代表已实际购票。</p><div class="row"><label>查看方式 <select id="ticketView"><option value="latest">最近一期（默认）</option><option value="overview">总览</option><option value="period">按期号</option><option value="date">按日期</option></select></label><label id="periodFilter" class="hidden">期号 <input id="periodQuery" placeholder="输入完整期号"></label><label id="dateFilter" class="hidden">日期 <input id="dateQuery" type="date"></label><button id="applyTicketFilter" class="secondary">查询</button></div><div id="ticketHistory" class="muted">暂无记录</div></article><article class="card wide"><h2>号码频率与信息熵</h2><p class="muted">H(X)=−Σ p(x)log₂p(x)。均匀分布时熵达到 log₂(K)；值越低表示历史分布越集中，但不代表预测能力更强。</p><div id="charts"></div></article></section>
<footer class="muted" style="margin-top:24px">数据仅分析已导入记录；请遵守数据来源网站的使用规则。</footer></main>
<script>
const $=x=>document.getElementById(x);let games=[];async function refresh(){let d=await fetch('/api/data?game='+$('game').value).then(r=>r.json());$('total').textContent=d.total;$('latest').textContent=d.latest||'—';$('official').href=d.url;let c=$('charts');c.innerHTML='';for(let g of d.analysis){let box=document.createElement('div');box.innerHTML=`<h3>${g.label} <span class="muted" style="font-size:14px">H = ${g.entropy.toFixed(3)} / ${g.maxEntropy.toFixed(3)} bit</span></h3>`;let max=Math.max(1,...g.hits);g.hits.forEach((n,i)=>{box.innerHTML+=`<div class="barrow"><span class="n">${String(i+1).padStart(2,'0')}</span><div class="track"><div class="fill" style="width:${n/max*100}%"></div></div><span style="width:38px;text-align:right">${n}</span></div>`});c.append(box)}}
function flash(msg,err=false){$('msg').textContent=msg;$('msg').className=err?'error':''}
let autoStamp='';async function refreshAutoStatus(){try{let data=await fetch('/api/auto-status').then(r=>r.json()),all=data._all||{},stamp=Object.keys(data).filter(k=>k!=='_all').map(k=>data[k].updated_at||'').join('|'),names={ssq:'双色球',dlt:'大乐透','3d':'福彩3D',pls:'排列3',kl8:'快乐8'};if(stamp!==autoStamp&&games.length&&$('game').value){autoStamp=stamp;refresh();refreshTickets()}let pct=Math.max(0,Math.min(100,Number(all.progress)||0));$('autoProgressBar').style.width=pct+'%';$('autoProgressText').textContent='总体进度：'+pct+'% · '+(all.state||'等待启动')+(all.detail?' · '+all.detail:'');$('autoStatus').textContent='各品种：'+Object.entries(data).filter(([g])=>g!=='_all').map(([g,x])=>names[g]+' '+x.state+' '+(x.progress||0)+'%'+(x.detail?'（'+x.detail+'）':'')+(x.error?'：'+x.error:'')).join('；')}catch(e){}}
async function post(url,body){let r=await fetch(url,{method:'POST',body});let d=await r.json();if(!r.ok)throw Error(d.error||'请求失败');return d}
async function refreshTickets(){let all=await fetch('/api/tickets?game='+$('game').value).then(r=>r.json()),ts=all.slice(),mode=$('ticketView').value,query=mode==='period'?$('periodQuery').value.trim():mode==='date'?$('dateQuery').value:'';$('periodFilter').classList.toggle('hidden',mode!=='period');$('dateFilter').classList.toggle('hidden',mode!=='date');let settled=all.filter(t=>t.status==='已结算'),wins=settled.filter(t=>t.tier&&t.tier!=='未中奖').length,prize=settled.filter(t=>typeof t.prize==='number').reduce((a,t)=>a+t.prize,0);if(mode==='period')ts=all.filter(t=>t.status==='已结算'&&String(t.draw_period)===query);else if(mode==='date')ts=all.filter(t=>t.status==='已结算'&&t.draw_date===query);else if(mode==='latest'&&settled.length){let latest=settled.reduce((a,t)=>Number(t.draw_period)>Number(a)?t.draw_period:a,settled[0].draw_period);ts=settled.filter(t=>String(t.draw_period)===String(latest))}else if(mode==='latest')ts=all.filter(t=>t.status!=='已结算');if(mode==='overview')ts.sort((a,b)=>Number(b.draw_period||0)-Number(a.draw_period||0)||String(b.created_at).localeCompare(String(a.created_at)));let box=$('ticketHistory'),summary='<div class="stats"><div class="stat"><span class="muted">已生成</span><b>'+all.length+' 注</b></div><div class="stat"><span class="muted">已结算</span><b>'+settled.length+' 注</b></div><div class="stat"><span class="muted">中奖注数</span><b>'+wins+' 注</b></div><div class="stat"><span class="muted">可核算模拟奖金</span><b>¥'+prize.toFixed(2)+'</b></div></div>';if(!ts.length){box.innerHTML=summary+'<p>'+ (mode==='latest'?'最近一期还没有已保存号码结算结果；待开奖号码会在这里显示。':mode==='period'?'没有找到该期号的核对记录。':mode==='date'?'没有找到该日期的核对记录。':'暂无记录')+'</p>';return}let title=mode==='latest'&&ts[0].status==='已结算'?'<p>最近核对：第 '+ts[0].draw_period+' 期'+(ts[0].draw_date?' · '+ts[0].draw_date:'')+'</p>':mode==='period'?'<p>期号查询：'+query+'</p>':mode==='date'?'<p>日期查询：'+query+'</p>':'';box.innerHTML=summary+title+ts.map(t=>{let balls=t.numbers.map((n,i)=>'<span class="ball '+($('game').value==='ssq'&&i<6?'red':'')+'">'+String(n).padStart(2,'0')+'</span>').join(''),draw=(t.draw_numbers||[]).map((n,i)=>'<span class="ball '+($('game').value==='ssq'&&i<6?'red':'')+'">'+String(n).padStart(2,'0')+'</span>').join(''),info=t.status==='已结算'?'开奖 '+(t.draw_date||'日期未记录')+' · 第 '+t.draw_period+' 期 · '+t.tier+' · 命中 '+t.hits.join('+')+(t.prize===null?'':' · 模拟奖金 ¥'+Number(t.prize).toFixed(2))+(t.prize_note?' · '+t.prize_note:'')+' · 生成于 '+t.created_at:'待开奖 · 生成于 '+t.created_at+' · 基准期 '+(t.base_period||'未同步');return '<div class="ticket"><div class="muted">'+info+'</div><div>你的号码：'+balls+'</div>'+(draw?'<div>开奖号码：'+draw+'</div>':'')+'</div>'}).join('')}
function renderExclude(){let g=games.find(x=>x.id===$('game').value);if(!g)return;let mode=g.id==='kl8'?'<label>快乐8玩法 <select id="kl8Pick">'+Array.from({length:10},(_,i)=>`<option value="${i+1}" ${i===9?'selected':''}>选${i+1}</option>`).join('')+'</select></label>':'';$('excludeControls').innerHTML=mode+g.groups.map((x,i)=>`<label>${x[0]}排除号码（可选，逗号或空格分隔） <input class="excluded" data-index="${i}" placeholder="例如：03, 12"></label>`).join('')}
$('ticketView').onchange=()=>refreshTickets();refreshAutoStatus();setInterval(refreshAutoStatus,2000);$('applyTicketFilter').onclick=()=>refreshTickets();$('periodQuery').onkeydown=e=>{if(e.key==='Enter')refreshTickets()};$('dateQuery').onchange=()=>refreshTickets();fetch('/api/games').then(r=>r.json()).then(d=>{games=d;for(let g of games)$('game').add(new Option(g.name,g.id));renderExclude();refresh();refreshTickets()});$('game').onchange=()=>{renderExclude();refresh();refreshTickets()};
$('upload').onclick=async()=>{let f=$('file').files[0];if(!f)return flash('请先选择文件',true);let fd=new FormData;fd.append('file',f);try{let d=await post('/api/import?game='+$('game').value,fd);flash(`导入 ${d.added} 期，有效记录共 ${d.total} 期`);refresh();refreshTickets()}catch(e){flash(e.message,true)}};
$('download').onclick=async()=>{let b=$('download');b.disabled=true;b.textContent='正在连接官方开奖数据…';flash('正在下载历史记录，首次下载可能需要一些时间');try{let d=await post('/api/download?game='+$('game').value,new FormData);flash(`下载完成：新增 ${d.added} 期，当前共 ${d.total} 期（${d.source}官方数据）`);refresh();refreshTickets()}catch(e){flash('下载失败：'+e.message,true)}finally{b.disabled=false;b.textContent='自动下载/更新开奖数据'}};
$('importText').onclick=async()=>{let fd=new FormData;fd.append('text',$('paste').value);try{let d=await post('/api/import?game='+$('game').value,fd);flash(`导入 ${d.added} 期，有效记录共 ${d.total} 期`);refresh();refreshTickets()}catch(e){flash(e.message,true)}};
 $('generate').onclick=async()=>{let fd=new FormData;fd.append('count',$('amount').value);fd.append('kl8Pick',$('kl8Pick')?.value||'10');fd.append('excludePrevious',$('excludePrevious').checked?'1':'0');fd.append('exclusions',JSON.stringify([...document.querySelectorAll('.excluded')].map(x=>x.value)));try{let d=await post('/api/generate?game='+$('game').value,fd);$('tickets').innerHTML=d.tickets.map(ns=>'<div class="ticket">'+ns.map((n,i)=>`<span class="ball ${$('game').value==='ssq'&&i<6?'red':''}">${String(n).padStart(2,'0')}</span>`).join('')+'</div>').join('');flash(d.previousExcluded?'号码已生成并保存，自动排除最近一期号码':'号码已生成并保存');refreshTickets()}catch(e){flash(e.message,true)}};
</script>'''

class Handler(BaseHTTPRequestHandler):
    def log_message(self, *_): pass
    def send(self, body, status=200, content_type="application/json; charset=utf-8"):
        b = body.encode("utf-8") if isinstance(body, str) else body
        self.send_response(status); self.send_header("Content-Type", content_type); self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b)
    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        if u.path == "/": return self.send(PAGE, content_type="text/html; charset=utf-8")
        if u.path == "/api/auto-status":
            with AUTO_STATUS_LOCK: status=json.loads(json.dumps(AUTO_STATUS,ensure_ascii=False))
            return self.send(json.dumps(status,ensure_ascii=False))
        if u.path == "/api/games": return self.send(json.dumps([{"id": k, "name": v["name"], "groups": [[g[0],g[1],g[2],g[3]] for g in v["groups"]]} for k,v in GAMES.items()], ensure_ascii=False))
        if u.path == "/api/data":
            game=urllib.parse.parse_qs(u.query).get("game",["ssq"])[0]
            if game not in GAMES: return self.send('{"error":"未知彩种"}',400)
            rows=load_data().get(game,[]); rows.sort(key=lambda x:x["period"],reverse=True)
            return self.send(json.dumps({"total":len(rows),"latest":rows[0]["period"] if rows else "","url":GAMES[game]["url"],"analysis":analyze(game,rows)},ensure_ascii=False))
        if u.path == "/api/tickets":
            game=urllib.parse.parse_qs(u.query).get("game",["ssq"])[0]
            if game not in GAMES:return self.send('{"error":"未知彩种"}',400)
            tickets=[t for t in load_tickets() if t.get("game")==game]
            tickets.sort(key=lambda x:x.get("created_at",""),reverse=True)
            return self.send(json.dumps(tickets,ensure_ascii=False))
        self.send("Not found",404,"text/plain")
    def do_POST(self):
        u=urllib.parse.urlparse(self.path); game=urllib.parse.parse_qs(u.query).get("game",["ssq"])[0]
        if game not in GAMES:return self.send('{"error":"未知彩种"}',400)
        length=int(self.headers.get("Content-Length",0)); raw=self.rfile.read(length)
        try:
            if u.path=="/api/import":
                ctype=self.headers.get("Content-Type","")
                boundary=ctype.partition("boundary=")[2].encode()
                if not boundary: raise ValueError("未收到文件或文本")
                parts=raw.split(b"--"+boundary)
                payload=next((p.split(b"\r\n\r\n",1)[1].rsplit(b"\r\n",1)[0] for p in parts if b"name=\"file\"" in p or b"name=\"text\"" in p),b"")
                rows=parse_xlsx(payload,game) if payload[:2]==b"PK" else parse_rows(payload.decode("utf-8-sig",errors="replace"),game)
                if not rows: raise ValueError("没有识别到有效记录；请核对列顺序、号码范围和数据格式")
                with LOCK:
                    data=load_data(); old={r["period"]:r for r in data.get(game,[])}; before=len(old)
                    old.update({r["period"]:r for r in rows}); data[game]=list(old.values()); save_data(data)
                    settle_tickets(game,list(old.values()))
                return self.send(json.dumps({"added":len(old)-before,"total":len(old)}))
            if u.path=="/api/download":
                result=sync_game(game,full=True)
                source="福利彩票" if game in ("ssq","3d","kl8") else "体育彩票"
                return self.send(json.dumps({"added":result["added"],"total":result["total"],"source":source},ensure_ascii=False))
            if u.path=="/api/generate":
                count=int(re.search(rb'name="count"\r\n\r\n(\d+)',raw).group(1)) if b'name="count"' in raw else 5
                rows=load_data().get(game,[])
                boundary=self.headers.get("Content-Type","").partition("boundary=")[2].encode()
                fields={}
                for part in raw.split(b"--"+boundary):
                    name=re.search(rb'name="([^"]+)"',part)
                    if name and b"\r\n\r\n" in part:
                        fields[name.group(1).decode()]=part.split(b"\r\n\r\n",1)[1].rsplit(b"\r\n",1)[0].decode(errors="ignore")
                manual=json.loads(fields.get('exclusions','[]'))
                if not isinstance(manual,list): manual=[]
                manual=(manual+[""]*len(GAMES[game]["groups"]))[:len(GAMES[game]["groups"])]
                exclusions=[]
                previous_excluded=False
                previous=max(rows,key=lambda r:int(r["period"])) if rows else None
                offset=0
                for i,(_,maximum,amount,_) in enumerate(GAMES[game]["groups"]):
                    group=set()
                    if fields.get('excludePrevious')=='1' and previous:
                        group.update(previous["numbers"][offset:offset+amount]); previous_excluded=True
                    for token in re.findall(r"\d+",manual[i]):
                        n=int(token)
                        if 1 <= n <= maximum: group.add(n)
                    exclusions.append(sorted(group)); offset+=amount
                selection_count=max(1,min(int(fields.get("kl8Pick","10")),10))
                tickets=generate(game,rows,max(1,min(count,20)),exclusions=exclusions,selection_count=selection_count)
                base=max((int(r["period"]) for r in rows),default=None)
                now=dt.datetime.now().astimezone().isoformat(timespec="seconds")
                with LOCK:
                    saved=load_tickets()
                    for numbers in tickets:
                        saved.append({"id":uuid.uuid4().hex[:10],"game":game,"numbers":numbers,"selection_count":selection_count if game=="kl8" else None,"created_at":now,"base_period":base,"status":"待开奖","prize":None})
                    save_tickets(saved)
                return self.send(json.dumps({"tickets":tickets,"previousExcluded":previous_excluded,"saved":len(tickets)}))
            self.send('{"error":"未知接口"}',404)
        except Exception as e:self.send(json.dumps({"error":str(e)},ensure_ascii=False),400)

if __name__ == "__main__":
    import argparse, webbrowser
    parser=argparse.ArgumentParser(description="本地彩票历史数据分析网页")
    parser.add_argument("--host",default="127.0.0.1");parser.add_argument("--port",type=int,default=8787);parser.add_argument("--no-browser",action="store_true")
    args=parser.parse_args();server=ThreadingHTTPServer((args.host,args.port),Handler)
    threading.Thread(target=auto_update_loop,name="lottery-auto-updater",daemon=True).start()
    print(f"打开 http://{args.host}:{args.port} （Ctrl+C 停止）")
    if not args.no_browser:threading.Timer(.7,lambda:webbrowser.open(f"http://{args.host}:{args.port}")).start()
    try:server.serve_forever()
    except KeyboardInterrupt:pass
    finally:server.server_close()
