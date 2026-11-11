"""本地彩票历史数据分析与随机选号网页（仅标准库，无第三方依赖）。"""
from __future__ import annotations

import csv
import datetime as dt
import html
import hashlib
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
FORECASTS_FILE = ROOT / "forecasts.json"
SIMULATIONS_FILE = ROOT / "simulation_frequencies.json"
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

def load_forecasts():
    try:
        value=json.loads(FORECASTS_FILE.read_text(encoding="utf-8"))
        return value if isinstance(value,list) else []
    except (OSError,json.JSONDecodeError):
        return []

def save_forecasts(forecasts):
    FORECASTS_FILE.write_text(json.dumps(forecasts,ensure_ascii=False,indent=2),encoding="utf-8")

def load_simulations():
    try:
        value=json.loads(SIMULATIONS_FILE.read_text(encoding="utf-8"))
        return value if isinstance(value,dict) else {}
    except (OSError,json.JSONDecodeError):
        return {}

def save_simulations(simulations):
    SIMULATIONS_FILE.write_text(json.dumps(simulations,ensure_ascii=False,indent=2),encoding="utf-8")

def _draw_signature(rows):
    canonical=[(str(r["period"]),r["numbers"]) for r in sorted(rows,key=lambda x:int(x["period"]))]
    payload=json.dumps(canonical,separators=(",",":"),ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()

def settle_forecasts(game, rows):
    """Settle each saved strategy against the first draw after its base period."""
    forecasts=load_forecasts()
    changed=False
    for record in forecasts:
        if record.get("game")!=game or record.get("status")!="待开奖":
            continue
        base=record.get("base_period")
        if base is None:continue
        later=[r for r in rows if int(r["period"])>int(base)]
        if not later:continue
        draw=min(later,key=lambda r:int(r["period"]))
        record.update(draw_period=draw["period"],draw_date=draw.get("date"),draw_numbers=draw["numbers"])
        forecast_date=str(record.get("created_at", ""))[:10]
        result_date=str(draw.get("date") or "")
        if not result_date:
            record["status"]="时间无法核验"
            record["settlement_note"]="开奖日期缺失，未计入前瞻对照统计。"
        elif forecast_date>=result_date:
            record["status"]="未纳入对照"
            record["settlement_note"]="记录日期不早于开奖日期，无法确认这是开奖前预测。"
        else:
            for entry in record.get("strategies",{}).values():
                entry["hits"]=score_ticket(game,entry["numbers"],draw)["hits"]
            record["status"]="已结算"
        changed=True
    if changed:save_forecasts(forecasts)
    return forecasts

def create_forecast(game, rows):
    ordered=sorted(rows,key=lambda r:int(r["period"]))
    if len(ordered)<60:raise ValueError("至少需要 60 期历史开奖，才能生成神经网络预测记录。")
    base=max(int(r["period"]) for r in ordered)
    import neural_backtest
    nn_groups=neural_backtest._next_suggestions(game,ordered)
    nn_numbers=[n for group in nn_groups for n in group["numbers"]]
    bayes_weights=posterior_weights(game,ordered)
    bayes_rankings=[]
    for group_weights in bayes_weights:
        bayes_rankings.append([[{"rank":rank,"number":n,"score":round(scores[n-1],6)}
                                for rank,n in enumerate(sorted(range(1,len(scores)+1),key=lambda x:(-scores[x-1],x)),1)]
                               for scores in group_weights])
    selection_count=20 if game=="kl8" else 10
    bayes_numbers=generate(game,ordered,count=1,selection_count=selection_count)[0]
    random_numbers=generate(game,[],count=1,selection_count=selection_count)[0]
    return {"id":uuid.uuid4().hex[:12],"game":game,"base_period":str(base),
            "created_at":dt.datetime.now().astimezone().isoformat(timespec="seconds"),
            "method_versions":{"neural":"mlp-12-window5-20-v1","bayes":"dirichlet-alpha20-v1","random":"uniform-v1"},
            "rankings":{"neural":[g["rankings"] for g in nn_groups],"bayes":bayes_rankings},
            "status":"待开奖","strategies":{
                "neural":{"numbers":nn_numbers,"hits":None},
                "bayes":{"numbers":bayes_numbers,"hits":None},
                "random":{"numbers":random_numbers,"hits":None}},
            "draw_period":None,"draw_date":None,"draw_numbers":None}

def simulate_frequencies(game, rows, source, trials):
    if source not in ("uniform","bayes","neural"):raise ValueError("未知模拟权重来源。")
    if len(rows)<1:raise ValueError("请先导入该彩种的历史开奖数据。")
    if source=="uniform":
        weights=posterior_weights(game,[])
    elif source=="bayes":
        weights=posterior_weights(game,rows)
    else:
        if len(rows)<60:raise ValueError("神经网络模拟至少需要 60 期历史开奖。")
        import neural_backtest
        weights=[group["scores"] for group in neural_backtest._next_suggestions(
            game,sorted(rows,key=lambda r:int(r["period"])))]
    groups=GAMES[game]["groups"]
    counts=[]
    for gi,(_,maximum,amount,_) in enumerate(groups):
        positions=amount if game in ("3d","pls") else 1
        counts.append([[0]*maximum for _ in range(positions)])
    for _ in range(trials):
        offset=0
        for gi,(_,maximum,amount,sorted_group) in enumerate(groups):
            if game=="kl8":amount=20
            positions=amount if game in ("3d","pls") else 1
            if positions>1:
                for pos in range(positions):
                    selected=random.choices(range(1,maximum+1),weights=weights[gi][pos],k=1)[0]
                    counts[gi][pos][selected-1]+=1
            elif sorted_group or group_counts is not None:
                pool=list(range(1,maximum+1))
                for _pick in range(amount):
                    selected=random.choices(pool,weights=[weights[gi][0][n-1] for n in pool],k=1)[0]
                    counts[gi][0][selected-1]+=1;pool.remove(selected)
            else:
                for selected in random.choices(range(1,maximum+1),weights=weights[gi][0],k=amount):
                    counts[gi][0][selected-1]+=1
            offset+=groups[gi][2]
    result_groups=[]
    for gi,(label,_,_,_) in enumerate(groups):
        positions=[]
        for pos,frequencies in enumerate(counts[gi]):
            positions.append({"position":pos+1 if game in ("3d","pls") else None,
                              "ranking":[{"rank":rank,"number":n,"count":frequencies[n-1],
                                          "frequency":round(frequencies[n-1]/trials,6)}
                                         for rank,n in enumerate(sorted(range(1,len(frequencies)+1),
                                                                         key=lambda x:(-frequencies[x-1],x)),1)]})
        result_groups.append({"label":label,"positions":positions})
    frequency_weights=[[[count+1 for count in frequencies] for frequencies in group] for group in counts]
    return {"game":game,"source":source,"trials":trials,
            "base_period":max((str(r["period"]) for r in rows),key=int) if rows else None,
            "data_signature":_draw_signature(rows),
            "created_at":dt.datetime.now().astimezone().isoformat(timespec="seconds"),
            "groups":result_groups,"weights":frequency_weights,"sourceWeights":weights}

def _paired_forecast_summary(records, first, second):
    diffs=[sum(r["strategies"][first]["hits"])-sum(r["strategies"][second]["hits"])
           for r in records]
    if not diffs:return {"mean":None,"ci95":None}
    mean=sum(diffs)/len(diffs)
    if len(diffs)<30:return {"mean":round(mean,4),"ci95":None}
    rng=random.Random(9137)
    means=sorted(sum(diffs[rng.randrange(len(diffs))] for _ in diffs)/len(diffs)
                 for _ in range(1000))
    return {"mean":round(mean,4),"ci95":[round(means[int(.025*999)],4),round(means[int(.975*999)],4)]}

def forecast_report(game):
    records=[r for r in load_forecasts() if r.get("game")==game]
    settled=[r for r in records if r.get("status")=="已结算"]
    strategies={}
    for key in ("neural","bayes","random"):
        vals=[sum(r["strategies"][key]["hits"]) for r in settled]
        strategies[key]={"meanHits":round(sum(vals)/len(vals),4) if vals else None,"count":len(vals)}
    return {"records":sorted(records,key=lambda r:r.get("created_at",""),reverse=True),
            "summary":{"settledCount":len(settled),"strategies":strategies,
                       "neuralMinusRandom":_paired_forecast_summary(settled,"neural","random"),
                       "bayesMinusRandom":_paired_forecast_summary(settled,"bayes","random"),
                       "excludedCount":sum(r.get("status") in ("未纳入对照","时间无法核验") for r in records)}}

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
        if ticket.get("ticket_type")=="multiple":
            result=score_multiple(game,ticket["numbers"],draw,ticket.get("group_counts"))
            ticket.update(result)
            ticket["tier"]=f"复式中{result['winning_lines']}注" if result["winning_lines"] else "未中奖"
        else:
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

def _multiple_tier(game, hits):
    if game=="ssq":
        red,blue=hits
        return 1 if red==6 and blue==1 else 2 if red==6 else 3 if red==5 and blue==1 else 4 if red==5 or (red==4 and blue==1) else 5 if red==4 or (red==3 and blue==1) else 6 if blue==1 else 0
    front,back=hits
    return 1 if (front,back)==(5,2) else 2 if (front,back)==(5,1) else 3 if (front,back) in ((5,0),(4,2)) else 4 if (front,back)==(4,1) else 5 if (front,back) in ((4,0),(3,2)) else 6 if (front,back) in ((3,1),(2,2)) else 7 if (front,back) in ((3,0),(2,1),(1,2),(0,2)) else 0

def score_multiple(game, numbers, draw, group_counts=None):
    """Count winning single lines in a multiple ticket without expanding combinations."""
    specs=GAMES[game]["groups"]
    group_counts=group_counts or ([len(numbers)-1,1] if game=="ssq" else [len(numbers)-2,2])
    group_choices=[]; offset=0
    for gi,(_, maximum, required, _) in enumerate(specs):
        amount=group_counts[gi]
        selected=set(numbers[offset:offset+amount]); actual=set(draw["numbers"][offset:offset+required])
        hit_count=len(selected & actual); miss_count=len(selected)-hit_count
        group_choices.append({h:math.comb(hit_count,h)*math.comb(miss_count,required-h)
                              for h in range(required+1) if 0<=required-h<=miss_count and h<=hit_count})
        offset+=amount
    tiers={}; best_hits=[0,0]
    for a,ca in group_choices[0].items():
        for b,cb in group_choices[1].items():
            ways=ca*cb; tier=_multiple_tier(game,(a,b))
            if (a,b)>(best_hits[0],best_hits[1]):best_hits=[a,b]
            if tier:
                tiers[tier]=tiers.get(tier,0)+ways
    known_total=0.0; unknown=False
    fixed={3:3000,4:200,5:10,6:5} if game=="ssq" else {}
    for tier,count in tiers.items():
        award=_award_value(draw,tier)
        if award is None:award=fixed.get(tier)
        if award is None:unknown=True
        else:known_total+=award*count
    combos=math.prod(math.comb(group_counts[i],spec[2]) for i,spec in enumerate(specs))
    return {"hits":best_hits,"tier_counts":{str(k):v for k,v in sorted(tiers.items())},
            "winning_lines":sum(tiers.values()),"combo_count":combos,
            "prize":None if unknown else round(known_total,2),
            "prize_note":"有中奖组合的奖级奖金数据不全，金额为已知部分；复式按各单式组合累计。" if unknown else ""}

def _multiple_draw_result(game, numbers, group_counts, draws, random_mode=False):
    tiers={}; any_prize=0; known=0.0; unknown=0; hit_totals=[0,0]; max_hits=0
    for draw in draws:
        result=score_multiple(game,numbers,draw,group_counts)
        for tier,count in result["tier_counts"].items():tiers[tier]=tiers.get(tier,0)+count
        if result["winning_lines"]:any_prize+=1
        if result["prize"] is None:unknown+=1
        else:known+=result["prize"]
        hit_totals=[a+b for a,b in zip(hit_totals,result["hits"])]
        max_hits=max(max_hits,result["winning_lines"])
    n=len(draws)
    return {"draws":n,"draws_with_prize":any_prize,"mean_best_hits":[round(x/n,4) for x in hit_totals] if n else [None,None],
            "tier_lines":tiers,"known_prize_total":round(known,2),"unknown_prize_draws":unknown,
            "max_winning_lines_in_one_draw":max_hits,"random_mode":random_mode}

def simulate_multiple(game, numbers, group_counts, trials):
    rows=sorted(load_data().get(game,[]),key=lambda r:int(r["period"]))
    historical=_multiple_draw_result(game,numbers,group_counts,rows)
    specs=GAMES[game]["groups"]
    random_draws=[]
    for _ in range(trials):
        random_draws.append(sorted(random.sample(range(1, specs[0][1]+1),specs[0][2]))+
                             sorted(random.sample(range(1, specs[1][1]+1),specs[1][2])))
    return {"historical":historical,"random":_multiple_draw_result(game,numbers,group_counts,random_draws,True),
            "history_note":"历史回放是对已有开奖的回看；复式号码由当前数据生成，不构成严格的前向回测证据。",
            "random_note":"随机模拟按官方号码范围均匀抽样；奖金金额不作模拟预测。"}

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

def generate(game, rows, count=5, temperature=1.0, exclusions=None, selection_count=10, weights=None, group_counts=None):
    weights = weights if weights is not None else posterior_weights(game, rows)
    exclusions = exclusions or [[] for _ in GAMES[game]["groups"]]
    out = []
    for _ in range(count):
        ticket = []
        for gi, (_, maximum, amount, sorted_group) in enumerate(GAMES[game]["groups"]):
            if group_counts is not None: amount=group_counts[gi]
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
                if sorted_group or group_counts is not None: values.sort()
            else:
                values = random.choices(pool, weights=[w[n - 1] for n in pool], k=amount)
            ticket.extend(values)
        out.append(ticket)
    return out

def rolling_backtest(game, rows, min_history=100, limit=500):
    """Compare historical-frequency forecasts with the uniform lottery baseline.

    Uses only draws strictly before each test draw, so no future data leaks into
    the forecast. The score is expected number of matching selected numbers.
    """
    ordered = sorted(rows, key=lambda r: int(r["period"]))
    if len(ordered) < 2:
        return {"tested": 0, "message": "至少需要两期历史数据。"}
    start = max(1, len(ordered) - limit, min_history)
    if start >= len(ordered):
        start = max(1, len(ordered) // 2)
    tested = ordered[start:]
    totals = [0.0 for _ in GAMES[game]["groups"]]
    baselines = [0.0 for _ in totals]
    for i, draw in enumerate(tested, start=start):
        weights = posterior_weights(game, ordered[:i])
        for gi, (_, maximum, amount, _) in enumerate(GAMES[game]["groups"]):
            if game == "kl8": amount = 20
            actual = draw["numbers"]
            lo = sum(g[2] for g in GAMES[game]["groups"][:gi])
            if game in ("3d", "pls"):
                # Positional forecasts are scored against the matching position.
                scores = [weights[gi][pos][actual[pos]-1] for pos in range(amount)]
                totals[gi] += sum(scores)
                baselines[gi] += amount / maximum
            else:
                values = actual[lo:lo+amount]
                totals[gi] += sum(weights[gi][0][n-1] for n in values) * amount
                baselines[gi] += amount * amount / maximum
    groups = []
    for gi, (label, _, _, _) in enumerate(GAMES[game]["groups"]):
        groups.append({"label": label, "model": round(totals[gi] / len(tested), 4),
                       "random": round(baselines[gi] / len(tested), 4)})
    return {"tested": len(tested), "firstPeriod": tested[0]["period"],
            "lastPeriod": tested[-1]["period"], "groups": groups,
            "message": "每期只用此前数据估计；历史表现不代表未来优势。"}

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
                settle_forecasts(game,list(old.values()))
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
<article class="card"><h2>贝叶斯号码建议</h2><p class="muted">对每个号码采用对称 Dirichlet 先验 α=20，后验概率为 (出现次数 + α/K) / (总次数 + α)。</p><label><input id="excludePrevious" type="checkbox"> 排除最近一期号码（仅作个人筛选，不提高中奖概率）</label><div id="excludeControls"></div><div class="row"><label>票型 <select id="ticketMode"><option value="single">单式</option><option value="multiple">复式（仅双色球/大乐透）</option></select></label><div id="multipleControls" class="hidden"></div></div><div id="multipleCost" class="muted"></div><div class="row"><label>生成注数 <select id="amount"><option>5</option><option>1</option><option>10</option><option>20</option></select></label><label>&#21495;&#30721;&#26435;&#37325; <select id="weightSource"><option value="bayes">&#36125;&#21494;&#26031;&#21518;&#39564;</option><option value="simulation">&#27169;&#25311;&#39057;&#29575;</option></select></label><button id="generate">生成参考号码</button></div><div id="tickets"></div></article>
<article class="card wide"><h2>已保存号码与开奖核对</h2><p class="muted">每次生成会自动保存，并等待生成基准期之后的下一期结果。默认查看最近一期；也可查总览、期号或日期。下载或导入新开奖后自动结算。奖金为一注2元单式投注的模拟税前金额，不代表已实际购票。</p><div class="row"><label>查看方式 <select id="ticketView"><option value="latest">最近一期（默认）</option><option value="overview">总览</option><option value="period">按期号</option><option value="date">按日期</option></select></label><label id="periodFilter" class="hidden">期号 <input id="periodQuery" placeholder="输入完整期号"></label><label id="dateFilter" class="hidden">日期 <input id="dateQuery" type="date"></label><button id="applyTicketFilter" class="secondary">查询</button></div><div id="ticketHistory" class="muted">暂无记录</div></article><article class="card wide"><h2>号码频率与信息熵</h2><p class="muted">H(X)=−Σ p(x)log₂p(x)。均匀分布时熵达到 log₂(K)；值越低表示历史分布越集中，但不代表预测能力更强。</p><div id="charts"></div></article><article class="card wide"><h2>历史滚动回测</h2><p class="muted">每期只使用此前开奖数据估计号码权重，再与随机均匀选号的理论命中数比较。此回测用于检查历史拟合，不代表下一期有优势。</p><div id="backtest" class="muted">计算中…</div><p><button id="trainNN">&#35757;&#32451;&#31070;&#32463;&#32593;&#32476;&#24182;&#36816;&#34892;&#26102;&#38388;&#39034;&#24207;&#22238;&#27979;</button></p><div id="nnResult" class="muted">&#23578;&#26410;&#35757;&#32451;&#31070;&#32463;&#32593;&#32476;&#12290;</div></article><article class="card wide"><h2>&#24320;&#22870;&#21069;&#39044;&#27979;&#35760;&#24405;&#19982;&#23545;&#29031;&#32452;</h2><p class="muted">&#27599;&#20010;&#22522;&#20934;&#26399;&#20445;&#23384;&#19968;&#32452;&#19981;&#21487;&#20462;&#25913;&#30340;&#31070;&#32463;&#32593;&#32476;&#12289;&#36125;&#21494;&#26031;&#21644;&#22343;&#21248;&#38543;&#26426;&#39044;&#27979;&#12290;&#26032;&#24320;&#22870;&#25968;&#25454;&#23548;&#20837;&#21518;&#33258;&#21160;&#32467;&#31639;&#12290;</p><button id="saveForecast">&#29983;&#25104;&#24182;&#20445;&#23384;&#19977;&#32452;&#39044;&#27979;</button><p id="forecastSummary" class="muted">&#26242;&#26080;&#39044;&#27979;&#35760;&#24405;</p><div id="forecastRecords"></div></article><article class="card wide"><h2>&#21495;&#30721;&#35780;&#20998;&#25490;</h2><p class="muted">&#31070;&#32463;&#32593;&#32476;&#21644;&#36125;&#21494;&#26031;&#20998;&#24320;&#25490;&#21015;&#21495;&#30721;&#12290;&#35780;&#20998;&#20195;&#34920;&#27169;&#22411;&#30456;&#23545;&#35780;&#20998;&#12289;&#19981;&#26159;&#19979;&#19968;&#26399;&#30495;&#23454;&#27010;&#29575;&#12290;</p><button id="loadRanks">&#35745;&#31639;&#24403;&#21069;&#25490;&#34892;</button><div id="rankingsView" class="muted"></div></article><article class="card wide"><h2>&#27169;&#25311;&#24320;&#22870;&#19982;&#21495;&#30721;&#39057;&#29575;</h2><p class="muted">&#36873;&#25321;&#22343;&#21248;&#12289;&#36125;&#21494;&#26031;&#25110;&#31070;&#32463;&#32593;&#32476;&#26435;&#37325;&#36827;&#34892;&#22810;&#27425;&#27169;&#25311;&#24320;&#22870;&#12290;&#39057;&#29575;&#26469;&#33258;&#36825;&#20010;&#27169;&#25311;&#35268;&#21017;&#12290;</p><div class="row"><label>&#27169;&#25311;&#27425;&#25968; <input id="simTrials" type="number" min="100" max="100000" step="100" value="10000"></label><label>&#27169;&#25311;&#26435;&#37325; <select id="simSource"><option value="uniform">&#22343;&#21248;&#38543;&#26426;</option><option value="bayes">&#36125;&#21494;&#26031;</option><option value="neural">&#31070;&#32463;&#32593;&#32476;</option></select></label><button id="runSimulation">&#36816;&#34892;&#27169;&#25311;&#24182;&#32479;&#35745;&#39057;&#29575;</button></div><p id="simSummary" class="muted"></p><div id="simResults"></div><p class="muted">&#27169;&#25311;&#39057;&#29575;&#21482;&#21453;&#26144;&#25152;&#36873;&#35268;&#30340;&#37319;&#26679;&#35268;&#21017;&#21644;&#27169;&#25311;&#27425;&#25968;&#12289;&#19981;&#26159;&#30495;&#23454;&#24320;&#22870;&#27010;&#29575;&#12290;</p></article></section>
<footer class="muted" style="margin-top:24px">数据仅分析已导入记录；请遵守数据来源网站的使用规则。</footer></main>
<script>
function multipleSummary(d){let fmt=x=>{let tiers=Object.entries(x.tier_lines||{}).map(([k,v])=>k+'等奖 '+v+' 注').join('、')||'无中奖组合';return '开奖样本 '+x.draws+' 次；有奖 '+x.draws_with_prize+' 次；平均各区命中 '+(x.mean_best_hits||[]).join('+')+'；'+tiers+'；已知奖金合计 ¥'+Number(x.known_prize_total||0).toFixed(2)+'；奖金未知样本 '+x.unknown_prize_draws+' 次'};return '历史回放：'+fmt(d.historical)+'。随机模拟（'+d.trials+' 次）：'+fmt(d.random)+'。'+d.history_note+' '+d.random_note}
const $=x=>document.getElementById(x);let games=[];async function refresh(){let d=await fetch('/api/data?game='+$('game').value).then(r=>r.json());$('total').textContent=d.total;$('latest').textContent=d.latest||'—';$('official').href=d.url;let c=$('charts');c.innerHTML='';for(let g of d.analysis){let box=document.createElement('div');box.innerHTML=`<h3>${g.label} <span class="muted" style="font-size:14px">H = ${g.entropy.toFixed(3)} / ${g.maxEntropy.toFixed(3)} bit</span></h3>`;let max=Math.max(1,...g.hits);g.hits.forEach((n,i)=>{box.innerHTML+=`<div class="barrow"><span class="n">${String(i+1).padStart(2,'0')}</span><div class="track"><div class="fill" style="width:${n/max*100}%"></div></div><span style="width:38px;text-align:right">${n}</span></div>`});c.append(box)}let b=await fetch('/api/backtest?game='+$('game').value).then(r=>r.json());$('backtest').textContent=b.tested?`测试 ${b.tested} 期（${b.firstPeriod} 至 ${b.lastPeriod}）：`+b.groups.map(x=>`${x.label}：模型加权命中 ${x.model}，随机基准 ${x.random}`).join('；')+'。'+b.message:b.message}
function flash(msg,err=false){$('msg').textContent=msg;$('msg').className=err?'error':''}
let autoStamp='';async function refreshAutoStatus(){try{let data=await fetch('/api/auto-status').then(r=>r.json()),all=data._all||{},stamp=Object.keys(data).filter(k=>k!=='_all').map(k=>data[k].updated_at||'').join('|'),names={ssq:'双色球',dlt:'大乐透','3d':'福彩3D',pls:'排列3',kl8:'快乐8'};if(stamp!==autoStamp&&games.length&&$('game').value){autoStamp=stamp;refresh();refreshTickets()}let pct=Math.max(0,Math.min(100,Number(all.progress)||0));$('autoProgressBar').style.width=pct+'%';$('autoProgressText').textContent='总体进度：'+pct+'% · '+(all.state||'等待启动')+(all.detail?' · '+all.detail:'');$('autoStatus').textContent='各品种：'+Object.entries(data).filter(([g])=>g!=='_all').map(([g,x])=>names[g]+' '+x.state+' '+(x.progress||0)+'%'+(x.detail?'（'+x.detail+'）':'')+(x.error?'：'+x.error:'')).join('；')}catch(e){}}
async function post(url,body){let r=await fetch(url,{method:'POST',body});let d=await r.json();if(!r.ok)throw Error(d.error||'请求失败');return d}
async function refreshTickets(){let all=await fetch('/api/tickets?game='+$('game').value).then(r=>r.json()),ts=all.slice(),mode=$('ticketView').value,query=mode==='period'?$('periodQuery').value.trim():mode==='date'?$('dateQuery').value:'';$('periodFilter').classList.toggle('hidden',mode!=='period');$('dateFilter').classList.toggle('hidden',mode!=='date');let settled=all.filter(t=>t.status==='已结算'),wins=settled.filter(t=>t.tier&&t.tier!=='未中奖').length,prize=settled.filter(t=>typeof t.prize==='number').reduce((a,t)=>a+t.prize,0);if(mode==='period')ts=all.filter(t=>t.status==='已结算'&&String(t.draw_period)===query);else if(mode==='date')ts=all.filter(t=>t.status==='已结算'&&t.draw_date===query);else if(mode==='latest'&&settled.length){let latest=settled.reduce((a,t)=>Number(t.draw_period)>Number(a)?t.draw_period:a,settled[0].draw_period);ts=settled.filter(t=>String(t.draw_period)===String(latest))}else if(mode==='latest')ts=all.filter(t=>t.status!=='已结算');if(mode==='overview')ts.sort((a,b)=>Number(b.draw_period||0)-Number(a.draw_period||0)||String(b.created_at).localeCompare(String(a.created_at)));let box=$('ticketHistory'),summary='<div class="stats"><div class="stat"><span class="muted">已生成</span><b>'+all.length+' 注</b></div><div class="stat"><span class="muted">已结算</span><b>'+settled.length+' 注</b></div><div class="stat"><span class="muted">中奖注数</span><b>'+wins+' 注</b></div><div class="stat"><span class="muted">可核算模拟奖金</span><b>¥'+prize.toFixed(2)+'</b></div></div>';if(!ts.length){box.innerHTML=summary+'<p>'+ (mode==='latest'?'最近一期还没有已保存号码结算结果；待开奖号码会在这里显示。':mode==='period'?'没有找到该期号的核对记录。':mode==='date'?'没有找到该日期的核对记录。':'暂无记录')+'</p>';return}let title=mode==='latest'&&ts[0].status==='已结算'?'<p>最近核对：第 '+ts[0].draw_period+' 期'+(ts[0].draw_date?' · '+ts[0].draw_date:'')+'</p>':mode==='period'?'<p>期号查询：'+query+'</p>':mode==='date'?'<p>日期查询：'+query+'</p>':'';box.innerHTML=summary+title+ts.map(t=>{let balls=t.numbers.map((n,i)=>'<span class="ball '+($('game').value==='ssq'&&i<6?'red':'')+'">'+String(n).padStart(2,'0')+'</span>').join(''),draw=(t.draw_numbers||[]).map((n,i)=>'<span class="ball '+($('game').value==='ssq'&&i<6?'red':'')+'">'+String(n).padStart(2,'0')+'</span>').join(''),info=t.status==='已结算'?'开奖 '+(t.draw_date||'日期未记录')+' · 第 '+t.draw_period+' 期 · '+t.tier+' · 命中 '+t.hits.join('+')+(t.prize===null?'':' · 模拟奖金 ¥'+Number(t.prize).toFixed(2))+(t.prize_note?' · '+t.prize_note:'')+' · 生成于 '+t.created_at:'待开奖 · 生成于 '+t.created_at+' · 基准期 '+(t.base_period||'未同步');return '<div class="ticket"><div class="muted">'+info+'</div><div>你的号码：'+balls+'</div>'+(draw?'<div>开奖号码：'+draw+'</div>':'')+'</div>'}).join('')}
async function refreshForecasts(){let game=$('game').value,d=await fetch('/api/forecasts?game='+game).then(r=>r.json()),sm=d.summary,fmt=x=>x.mean===null?'暂无数据':x.mean+(x.ci95?' (95% CI '+x.ci95[0]+' to '+x.ci95[1]+')':' (n<30; CI omitted)'),labels={neural:'神经网络',bayes:'贝叶斯',random:'随机'};let vals=sm.strategies;$('forecastSummary').textContent='已结算 '+sm.settledCount+' 期 | 平均命中数 : 神经网络 '+(vals.neural.meanHits??'—')+' | 贝叶斯 '+(vals.bayes.meanHits??'—')+' | 随机 '+(vals.random.meanHits??'—')+' | 神经网络减随机 '+fmt(sm.neuralMinusRandom)+' | 贝叶斯减随机 '+fmt(sm.bayesMinusRandom)+' | 未纳入对照 '+sm.excludedCount+' 期';let box=$('forecastRecords');box.replaceChildren();for(let f of d.records){let card=document.createElement('div');card.className='ticket';let head=document.createElement('div');head.className='muted';head.textContent='基准期 '+f.base_period+' | '+(f.draw_period?'开奖期 '+f.draw_period+' | ':'')+f.status+' | 记录于 '+f.created_at;card.append(head);for(let key of ['neural','bayes','random']){let line=document.createElement('div'),entry=f.strategies[key],ns=entry.numbers.map(n=>String(n).padStart(2,'0')).join(' ');line.textContent=labels[key]+': '+ns+(entry.hits?' | 命中 '+entry.hits.join('+')+' | 合计 '+entry.hits.reduce((a,b)=>a+b,0):'');card.append(line)}if(f.settlement_note){let note=document.createElement('div');note.className='muted';note.textContent=f.settlement_note;card.append(note)}box.append(card)}}
$('saveForecast').onclick=async()=>{let b=$('saveForecast');b.disabled=true;b.textContent='训练并保存中';try{let d=await post('/api/forecast?game='+$('game').value,new FormData);flash(d.created?'已保存本基准期的三组开奖前预测':'本基准期已有预测记录。保留原记录');await refreshForecasts()}catch(e){flash(e.message,true)}finally{b.disabled=false;b.textContent='生成并保存三组预测'}};
function showSimulations(data){let box=$('simResults');box.replaceChildren();if(!data){$('simSummary').textContent='暂无模拟记录';return}$('simSummary').textContent='最近次数 '+data.trials+' 次 | 权重来源 '+({uniform:'均匀随机',bayes:'贝叶斯',neural:'神经网络'}[data.source]||data.source)+' | 基准期 '+(data.base_period||'?')+' | 时间 '+data.created_at+(data.stale?' | 模拟频率已过期、请重新运行模拟':'')+' | 可选择“号码权重”后按此模拟频率抽样';for(let group of data.groups){for(let pos of group.positions){let details=document.createElement('details');let summary=document.createElement('summary');summary.textContent=group.label+(pos.position?' - 位置 '+pos.position:'')+' - 完整频率排行';details.append(summary);for(let item of pos.ranking){let row=document.createElement('div');row.textContent=item.rank+'. '+String(item.number).padStart(2,'0')+' - '+item.count+' / '+data.trials+' ('+item.frequency+')';details.append(row)}box.append(details)}}}
async function refreshSimulation(){let d=await fetch('/api/simulation?game='+$('game').value).then(r=>r.json());showSimulations(d)}
$('loadRanks').onclick=async()=>{let b=$('loadRanks'),box=$('rankingsView');b.disabled=true;b.textContent='正在计算排行';box.replaceChildren();try{let r=await fetch('/api/rankings?game='+$('game').value,{method:'POST'}),d=await r.json();if(!r.ok)throw Error(d.error||'排行计算失败');for(let group of d.groups){let section=document.createElement('details'),summary=document.createElement('summary');summary.textContent=group.label+' - 展开完整排行';section.append(summary);for(let key of ['neural','bayes'])for(let pos=0;pos<group[key].length;pos++){let line=document.createElement('div'),arr=group[key][pos];line.textContent=(key==='neural'?'神经网络':'贝叶斯')+(group[key].length>1?' 位置 '+(pos+1):'')+': '+arr.map(x=>x.rank+'. '+String(x.number).padStart(2,'0')+' ('+x.score+')').join(' | ');section.append(line)}box.append(section)}let note=document.createElement('p');note.className='muted';note.textContent='排行分数是模型分数、不是真实开奖概率。';box.append(note)}catch(e){box.textContent=e.message}finally{b.disabled=false;b.textContent='计算当前排行'}};
$('runSimulation').onclick=async()=>{let b=$('runSimulation');b.disabled=true;b.textContent='正在模拟并统计';try{let r=await fetch('/api/simulate?game='+$('game').value,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({source:$('simSource').value,trials:Number($('simTrials').value)||10000})}),d=await r.json();if(!r.ok)throw Error(d.error||'模拟失败');showSimulations(d);flash('模拟频率已保存')}catch(e){flash(e.message,true)}finally{b.disabled=false;b.textContent='运行模拟并统计频率'}};
function renderExclude(){let g=games.find(x=>x.id===$('game').value);if(!g)return;let supported=['ssq','dlt'].includes(g.id);$('ticketMode').disabled=!supported;if(!supported)$('ticketMode').value='single';let mode=g.id==='kl8'?'<label>快乐8玩法 <select id="kl8Pick">'+Array.from({length:10},(_,i)=>`<option value="${i+1}" ${i===9?'selected':''}>选${i+1}</option>`).join('')+'</select></label>':'';$('excludeControls').innerHTML=mode+g.groups.map((x,i)=>`<label>${x[0]}排除号码（可选，逗号或空格分隔） <input class="excluded" data-index="${i}" placeholder="例如：03, 12"></label>`).join('');renderMultipleControls()}
function choose(n,k){if(k<0||k>n)return 0;let v=1;for(let i=1;i<=k;i++)v=v*(n-i+1)/i;return Math.round(v)}
function renderMultipleControls(){let g=games.find(x=>x.id===$('game').value),box=$('multipleControls'),on=!!g&&['ssq','dlt'].includes(g.id)&&$('ticketMode').value==='multiple';box.classList.toggle('hidden',!on);if(!on){$('multipleCost').textContent='';return}let specs=g.id==='ssq'?[['红球',6,33,7],['蓝球',1,16,2]]:[['前区',5,35,6],['后区',2,12,3]];box.innerHTML=specs.map((x,i)=>`<label>${x[0]}复式号码数 <input class="group-count" id="groupCount${i}" type="number" min="${x[1]}" max="${x[2]}" value="${x[3]}"></label>`).join('');box.querySelectorAll('input').forEach(x=>x.oninput=updateMultipleCost);updateMultipleCost()}
function updateMultipleCost(){let g=games.find(x=>x.id===$('game').value);if(!g||$('ticketMode').value!=='multiple')return;let a=Number($('groupCount0')?.value),b=Number($('groupCount1')?.value),need=g.id==='ssq'?[6,1]:[5,2],combos=choose(a,need[0])*choose(b,need[1]);$('multipleCost').textContent=`每组复式展开 ${combos.toLocaleString()} 注单式，模拟金额 ¥${(combos*2).toLocaleString()}（每注2元）`}
$('ticketView').onchange=()=>refreshTickets();refreshAutoStatus();setInterval(refreshAutoStatus,2000);$('applyTicketFilter').onclick=()=>refreshTickets();$('periodQuery').onkeydown=e=>{if(e.key==='Enter')refreshTickets()};$('dateQuery').onchange=()=>refreshTickets();fetch('/api/games').then(r=>r.json()).then(d=>{games=d;for(let g of games)$('game').add(new Option(g.name,g.id));renderExclude();refresh();refreshTickets();refreshForecasts();refreshSimulation()});$('game').onchange=()=>{renderExclude();refresh();refreshTickets();refreshForecasts();refreshSimulation()};
$('upload').onclick=async()=>{let f=$('file').files[0];if(!f)return flash('请先选择文件',true);let fd=new FormData;fd.append('file',f);try{let d=await post('/api/import?game='+$('game').value,fd);flash(`导入 ${d.added} 期，有效记录共 ${d.total} 期`);refresh();refreshTickets()}catch(e){flash(e.message,true)}};
$('download').onclick=async()=>{let b=$('download');b.disabled=true;b.textContent='正在连接官方开奖数据…';flash('正在下载历史记录，首次下载可能需要一些时间');try{let d=await post('/api/download?game='+$('game').value,new FormData);flash(`下载完成：新增 ${d.added} 期，当前共 ${d.total} 期（${d.source}官方数据）`);refresh();refreshTickets()}catch(e){flash('下载失败：'+e.message,true)}finally{b.disabled=false;b.textContent='自动下载/更新开奖数据'}};
$('importText').onclick=async()=>{let fd=new FormData;fd.append('text',$('paste').value);try{let d=await post('/api/import?game='+$('game').value,fd);flash(`导入 ${d.added} 期，有效记录共 ${d.total} 期`);refresh();refreshTickets()}catch(e){flash(e.message,true)}};
 $('ticketMode').onchange=renderMultipleControls;
 $('generate').onclick=async()=>{let fd=new FormData;fd.append('count',$('amount').value);fd.append('weightSource',$('weightSource').value);fd.append('kl8Pick',$('kl8Pick')?.value||'10');fd.append('excludePrevious',$('excludePrevious').checked?'1':'0');fd.append('ticketMode',$('ticketMode').value);fd.append('groupCount0',$('groupCount0')?.value||'');fd.append('groupCount1',$('groupCount1')?.value||'');fd.append('exclusions',JSON.stringify([...document.querySelectorAll('.excluded')].map(x=>x.value)));try{let d=await post('/api/generate?game='+$('game').value,fd),box=$('tickets');box.replaceChildren();for(let i=0;i<d.tickets.length;i++){let ns=d.tickets[i],card=document.createElement('div');card.className='ticket';let line=document.createElement('div');for(let j=0;j<ns.length;j++){let ball=document.createElement('span');ball.className='ball '+($('game').value==='ssq'&&j<d.groupCounts?.[0]?'red':'');ball.textContent=String(ns[j]).padStart(2,'0');line.append(ball)}card.append(line);if(d.ticketType==='multiple'){let rec=d.ticketRecords[i],meta=document.createElement('p');meta.className='muted';meta.textContent=`复式展开 ${rec.combo_count.toLocaleString()} 注 · 模拟金额 ¥${rec.cost.toLocaleString()}`;let trials=document.createElement('input');trials.type='number';trials.min='100';trials.max='100000';trials.step='100';trials.value='10000';trials.setAttribute('aria-label','随机模拟次数');let button=document.createElement('button');button.className='secondary';button.textContent='历史回放 + 随机模拟';let out=document.createElement('p');out.className='muted';button.onclick=async()=>{button.disabled=true;button.textContent='模拟中…';try{let r=await fetch('/api/multiple-simulate?game='+$('game').value,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id:rec.id,trials:Number(trials.value)||10000})}),result=await r.json();if(!r.ok)throw Error(result.error||'模拟失败');out.textContent=multipleSummary(result);refreshTickets()}catch(e){out.textContent=e.message}finally{button.disabled=false;button.textContent='重新运行历史回放 + 随机模拟'}};card.append(meta,trials,button,out)}box.append(card)}flash(d.previousExcluded?'号码已生成并保存，自动排除最近一期号码':'号码已生成并保存');refreshTickets()}catch(e){flash(e.message,true)}};
$('trainNN').onclick=async()=>{let b=$('trainNN'),box=$('nnResult');b.disabled=true;b.textContent='\u8bad\u7ec3\u4e0e\u56de\u6d4b\u8fdb\u884c\u4e2d\u2026';box.textContent='\u6309\u65f6\u95f4\u987a\u5e8f\u8bad\u7ec3\u5e76\u8bc4\u4f30\uff0c\u8bf7\u7a0d\u5019\u3002';try{let r=await fetch('/api/train?game='+$('game').value,{method:'POST'}),d=await r.json();if(!r.ok)throw Error(d.error||'\u8bad\u7ec3\u5931\u8d25');if(d.error){box.textContent=d.error;return}let f=x=>x.mean+' (95% CI '+x.ci95[0]+' to '+x.ci95[1]+')',p=d.nextSuggestedNumbers.map(g=>g.label+' '+g.numbers.join(',')).join(' / ');box.textContent='\u8bad\u7ec3\u671f '+d.trainFirst+'\u2013'+d.trainLast+'\uff08'+d.trainCount+'\u671f\uff09\uff1b\u6d4b\u8bd5\u671f '+d.testFirst+'\u2013'+d.testLast+'\uff08'+d.testCount+'\u671f\uff09\u3002\u5e73\u5747\u547d\u4e2d\uff1a\u795e\u7ecf\u7f51\u7edc '+d.meanHits.nn+'\uff0c\u8d1d\u53f6\u65af '+d.meanHits.bayes+'\uff0c\u968f\u673a\u57fa\u51c6 '+d.meanHits.random+'\u3002\u795e\u7ecf\u7f51\u7edc\u51cf\u968f\u673a '+f(d.nnMinusRandom)+'\uff1b\u51cf\u8d1d\u53f6\u65af '+f(d.nnMinusBayes)+'\u3002\u5224\u65ad\uff1a'+d.results.random+'\uff1b'+d.results.bayes+'\u3002\u4e0b\u4e00\u671f\u53c2\u8003\u53f7\u7801\uff1a'+p+'\u3002'+d.forecastNote+' '+d.warning}catch(e){box.textContent='\u8bad\u7ec3\u5931\u8d25\uff1a'+e.message}finally{b.disabled=false;b.textContent='\u8bad\u7ec3\u795e\u7ecf\u7f51\u7edc\u5e76\u8fd0\u884c\u65f6\u95f4\u987a\u5e8f\u56de\u6d4b'}};
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
        if u.path == "/api/backtest":
            rows=load_data().get(game,[])
            return self.send(json.dumps(rolling_backtest(game,rows),ensure_ascii=False))
        if u.path == "/api/simulation":
            game=urllib.parse.parse_qs(u.query).get("game",["ssq"])[0]
            if game not in GAMES:return self.send('{"error":"未知彩种"}',400)
            result=load_simulations().get(game)
            if result:
                rows=load_data().get(game,[])
                latest=max((int(r["period"]) for r in rows),default=None)
                result["stale"]=(latest is None or int(result.get("base_period") or 0)!=latest
                                  or result.get("data_signature")!=_draw_signature(rows))
            return self.send(json.dumps(result,ensure_ascii=False))
        if u.path == "/api/forecasts":
            game=urllib.parse.parse_qs(u.query).get("game",["ssq"])[0]
            if game not in GAMES:return self.send('{"error":"未知彩种"}',400)
            return self.send(json.dumps(forecast_report(game),ensure_ascii=False))
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
            if u.path=="/api/simulate":
                request=json.loads(raw.decode("utf-8") or "{}")
                source=request.get("source","uniform")
                trials=max(100,min(int(request.get("trials",10000)),100000))
                result=simulate_frequencies(game,load_data().get(game,[]),source,trials)
                with LOCK:
                    saved=load_simulations();saved[game]=result;save_simulations(saved)
                return self.send(json.dumps(result,ensure_ascii=False))
            if u.path=="/api/multiple-simulate":
                if game not in ("ssq","dlt"):raise ValueError("复式模拟目前仅支持双色球和大乐透。")
                request=json.loads(raw.decode("utf-8") or "{}")
                trials=max(100,min(int(request.get("trials",10000)),100000))
                ticket=next((t for t in load_tickets() if t.get("id")==request.get("id") and t.get("game")==game and t.get("ticket_type")=="multiple"),None)
                if not ticket:raise ValueError("找不到这条复式记录，请刷新后重试。")
                result=simulate_multiple(game,ticket["numbers"],ticket.get("group_counts"),trials)
                result.update({"trials":trials,"created_at":dt.datetime.now().astimezone().isoformat(timespec="seconds")})
                with LOCK:
                    saved=load_tickets()
                    for item in saved:
                        if item.get("id")==ticket["id"]:item["multiple_simulation"]=result
                    save_tickets(saved)
                return self.send(json.dumps(result,ensure_ascii=False))
            if u.path=="/api/rankings":
                rows=load_data().get(game,[])
                if len(rows)<60:raise ValueError("至少需要60期历史开奖数据。")
                import neural_backtest
                neural=neural_backtest._next_suggestions(game,sorted(rows,key=lambda r:int(r["period"])))
                bayes=posterior_weights(game,rows)
                groups=[]
                for gi,(label,_,_,_) in enumerate(GAMES[game]["groups"]):
                    bayes_rankings=[[{"rank":rank,"number":n,"score":round(scores[n-1],6)}
                                     for rank,n in enumerate(sorted(range(1,len(scores)+1),key=lambda x:(-scores[x-1],x)),1)]
                                    for scores in bayes[gi]]
                    groups.append({"label":label,"neural":neural[gi]["rankings"],"bayes":bayes_rankings})
                return self.send(json.dumps({"game":game,"groups":groups,
                    "note":"分数仅用于组内排名、不是下一期的真实概率。"},ensure_ascii=False))
            if u.path=="/api/forecast":
                rows=load_data().get(game,[])
                if len(rows)<60:raise ValueError("\u81f3\u5c11\u9700\u8981 60 \u671f\u5386\u53f2\u5f00\u5956\uff0c\u624d\u80fd\u5efa\u7acb\u9884\u6d4b\u8bb0\u5f55\u3002")
                base=str(max(int(r["period"]) for r in rows))
                existing=next((r for r in load_forecasts() if r.get("game")==game and r.get("base_period")==base),None)
                if existing:return self.send(json.dumps({"record":existing,"created":False},ensure_ascii=False))
                record=create_forecast(game,rows)
                with LOCK:
                    saved=load_forecasts()
                    existing=next((r for r in saved if r.get("game")==game and r.get("base_period")==base),None)
                    if existing:record=existing;created=False
                    else:
                        saved.append(record);save_forecasts(saved);created=True
                        latest_rows=load_data().get(game,[])
                        if latest_rows:
                            settle_forecasts(game,latest_rows)
                        record=next((r for r in load_forecasts() if r.get("id")==record["id"]),record)
                return self.send(json.dumps({"record":record,"created":created},ensure_ascii=False))
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
                    settle_forecasts(game,list(old.values()))
                return self.send(json.dumps({"added":len(old)-before,"total":len(old)}))
            if u.path=="/api/download":
                result=sync_game(game,full=True)
                source="福利彩票" if game in ("ssq","3d","kl8") else "体育彩票"
                return self.send(json.dumps({"added":result["added"],"total":result["total"],"source":source},ensure_ascii=False))
            if u.path=="/api/train":
                import neural_backtest
                rows=load_data().get(game,[])
                result=neural_backtest.train_and_backtest(game,rows)
                result_path=ROOT/"neural_backtest_results.json"
                try: saved=json.loads(result_path.read_text(encoding="utf-8"))
                except (OSError,json.JSONDecodeError): saved={}
                saved[game]=result
                result_path.write_text(json.dumps(saved,ensure_ascii=False,indent=2),encoding="utf-8")
                return self.send(json.dumps(result,ensure_ascii=False))
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
                ticket_mode=fields.get("ticketMode","single")
                group_counts=None
                if ticket_mode=="multiple":
                    if game not in ("ssq","dlt"):raise ValueError("复式目前仅支持双色球和大乐透。")
                    defaults=[7,2] if game=="ssq" else [6,3]
                    limits=[(6,33),(1,16)] if game=="ssq" else [(5,35),(2,12)]
                    group_counts=[int(fields.get(f"groupCount{i}",str(defaults[i]))) for i in range(2)]
                    if any(n<lo or n>hi for n,(lo,hi) in zip(group_counts,limits)):
                        raise ValueError("复式每区号码数量超出该玩法范围。")
                weights=None
                weight_source=fields.get("weightSource","bayes")
                if weight_source=="simulation":
                    simulation=load_simulations().get(game)
                    if not simulation:raise ValueError("请先运行模拟频率统计。")
                    latest=max((int(r["period"]) for r in rows),default=None)
                    if (latest is None or int(simulation.get("base_period") or 0)!=latest
                            or simulation.get("data_signature")!=_draw_signature(rows)):
                        raise ValueError("模拟频率已过期。请根据当前开奖数据重新运行模拟。")
                    weights=simulation.get("weights")
                tickets=generate(game,rows,max(1,min(count,20)),exclusions=exclusions,
                                selection_count=selection_count,weights=weights,group_counts=group_counts)
                base=max((int(r["period"]) for r in rows),default=None)
                now=dt.datetime.now().astimezone().isoformat(timespec="seconds")
                with LOCK:
                    saved=load_tickets()
                    records=[]
                    for numbers in tickets:
                        record={"id":uuid.uuid4().hex[:10],"game":game,"numbers":numbers,"selection_count":selection_count if game=="kl8" else None,"weight_source":weight_source,"created_at":now,"base_period":base,"status":"待开奖","prize":None}
                        if group_counts is not None:
                            combos=math.prod(math.comb(group_counts[i],spec[2]) for i,spec in enumerate(GAMES[game]["groups"]))
                            record.update({"ticket_type":"multiple","group_counts":group_counts,"combo_count":combos,"cost":combos*2,"multiple_simulation":None})
                        saved.append(record);records.append(record)
                    save_tickets(saved)
                shown_counts=group_counts or ([6,1] if game=="ssq" else None)
                return self.send(json.dumps({"tickets":tickets,"ticketRecords":records,"ticketType":ticket_mode,"groupCounts":shown_counts,"previousExcluded":previous_excluded,"saved":len(tickets),"weightSource":weight_source}))
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
