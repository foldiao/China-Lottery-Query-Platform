"""Dependency-free neural lottery experiment with a chronological holdout.

This is an evaluation tool, not a claim that random lottery draws are learnable.
"""
from __future__ import annotations

import json
import math
import random
import statistics
from pathlib import Path

import app

WINDOWS = (5, 20)
HIDDEN = 12
EPOCHS = 4
MAX_TRAIN = 1200
TEST_FRACTION = 0.20
BOOTSTRAPS = 1000


def _features(rows, index, lo, hi, maximum, position=None):
    values = []
    for window in WINDOWS:
        prior = rows[max(0, index - window):index]
        counts = [0] * maximum
        for row in prior:
            selected = [row["numbers"][lo + position]] if position is not None else row["numbers"][lo:hi]
            for n in selected:
                counts[n - 1] += 1
        denom = max(1, len(prior))
        values.extend(c / denom for c in counts)
    return values


def _sigmoid(x):
    if x >= 0:
        z = math.exp(-min(x, 30.0))
        return 1.0 / (1.0 + z)
    z = math.exp(max(x, -30.0))
    return z / (1.0 + z)


class TinyMLP:
    """Small one-hidden-layer classifier trained with deterministic SGD."""
    def __init__(self, inputs, outputs, seed):
        rng = random.Random(seed)
        self.w1 = [[rng.uniform(-0.08, 0.08) for _ in range(inputs)] for _ in range(HIDDEN)]
        self.b1 = [0.0] * HIDDEN
        self.w2 = [[rng.uniform(-0.08, 0.08) for _ in range(HIDDEN)] for _ in range(outputs)]
        self.b2 = [0.0] * outputs

    def forward(self, x):
        hidden = [math.tanh(sum(w * v for w, v in zip(row, x)) + b)
                  for row, b in zip(self.w1, self.b1)]
        output = [_sigmoid(sum(w * h for w, h in zip(row, hidden)) + b)
                  for row, b in zip(self.w2, self.b2)]
        return hidden, output

    def train(self, examples, amount, seed):
        rng = random.Random(seed)
        lr = 0.025
        positive_scale = max(1.0, (len(self.w2) - amount) / max(1, amount))
        for _ in range(EPOCHS):
            order = list(range(len(examples)))
            rng.shuffle(order)
            for ei in order:
                x, target = examples[ei]
                hidden, output = self.forward(x)
                delta2 = [(p - y) * (positive_scale if y else 1.0)
                          for p, y in zip(output, target)]
                delta1 = [sum(self.w2[j][i] * delta2[j] for j in range(len(delta2)))
                          * (1.0 - hidden[i] * hidden[i]) for i in range(HIDDEN)]
                for j, row in enumerate(self.w2):
                    err = delta2[j]
                    for i in range(HIDDEN):
                        row[i] -= lr * (err * hidden[i] + 0.0001 * row[i])
                    self.b2[j] -= lr * err
                for i, row in enumerate(self.w1):
                    err = delta1[i]
                    for j in range(len(x)):
                        row[j] -= lr * (err * x[j] + 0.0001 * row[j])
                    self.b1[i] -= lr * err


def _model_scores(game, rows, train_end, test_indices):
    groups = app.GAMES[game]["groups"]
    models = []
    offsets = []
    offset = 0
    for gi, (_, maximum, amount, _) in enumerate(groups):
        positions = amount if game in ("3d", "pls") else 1
        lo = offset
        hi = lo + amount
        models.append([])
        for pos in range(positions):
            examples = []
            start = 20
            first = max(start, train_end - MAX_TRAIN)
            for idx in range(first, train_end):
                x = _features(rows, idx, lo, hi, maximum, pos if positions > 1 else None)
                if positions > 1:
                    target = [1.0 if n == rows[idx]["numbers"][pos] else 0.0
                              for n in range(1, maximum + 1)]
                else:
                    selected = set(rows[idx]["numbers"][lo:hi])
                    target = [1.0 if n in selected else 0.0 for n in range(1, maximum + 1)]
                examples.append((x, target))
            if not examples:
                models[gi].append(None)
                continue
            net = TinyMLP(len(examples[0][0]), maximum, 1103 + gi * 13 + pos)
            net.train(examples, 1 if positions > 1 else amount, 2407 + gi * 17 + pos)
            models[gi].append(net)
        offsets.append((lo, hi))
        offset = hi

    predictions = {}
    for idx in test_indices:
        per_group = []
        for gi, (_, maximum, amount, _) in enumerate(groups):
            if game == "kl8": amount = 20
            lo, hi = offsets[gi]
            x = _features(rows, idx, lo, hi, maximum, pos if game in ("3d", "pls") else None)
            per_group.append([net.forward(x)[1] if net else [1.0 / maximum] * maximum
                              for net in models[gi]])
        predictions[idx] = per_group
    return predictions


def _next_suggestions(game, rows):
    """Refit on all known draws after evaluation and rank a next-draw candidate."""
    groups = app.GAMES[game]["groups"]
    suggestions = []
    offset = 0
    for gi, (label, maximum, amount, _) in enumerate(groups):
        positions = amount if game in ("3d", "pls") else 1
        lo, hi = offset, offset + amount
        picks = []
        scores_by_position = []
        ranks_by_position = []
        for pos in range(positions):
            first = max(20, len(rows) - MAX_TRAIN)
            examples = []
            for idx in range(first, len(rows)):
                x = _features(rows, idx, lo, hi, maximum, pos if positions > 1 else None)
                if positions > 1:
                    target = [1.0 if n == rows[idx]["numbers"][pos] else 0.0
                              for n in range(1, maximum + 1)]
                else:
                    selected = set(rows[idx]["numbers"][lo:hi])
                    target = [1.0 if n in selected else 0.0 for n in range(1, maximum + 1)]
                examples.append((x, target))
            net = TinyMLP(2 * maximum, maximum, 7103 + gi * 13 + pos)
            net.train(examples, 1 if positions > 1 else amount, 8407 + gi * 17 + pos)
            x = _features(rows, len(rows), lo, hi, maximum, pos if positions > 1 else None)
            scores = net.forward(x)[1]
            scores_by_position.append(scores)
            order = sorted(range(1, maximum + 1), key=lambda n: (-scores[n - 1], n))
            ranks_by_position.append([{"rank": rank, "number": n, "score": round(scores[n - 1], 6)}
                                      for rank, n in enumerate(order, 1)])
            picks.append(order[:1 if positions > 1 else (20 if game == "kl8" else amount)])
        if positions > 1:
            numbers = [pick[0] for pick in picks]
        else:
            numbers = picks[0]
            if groups[gi][3]:
                numbers.sort()
        suggestions.append({"label": label, "numbers": numbers,
                            "scores": scores_by_position, "rankings": ranks_by_position})
        offset = hi
    return suggestions


def _top(scores, count):
    return sorted(range(1, len(scores) + 1), key=lambda n: (-scores[n - 1], n))[:count]


def _percentile(values, p):
    values = sorted(values)
    if not values:
        return 0.0
    at = (len(values) - 1) * p
    lo = int(at)
    hi = min(lo + 1, len(values) - 1)
    return values[lo] + (values[hi] - values[lo]) * (at - lo)


def _ci(differences, seed):
    rng = random.Random(seed)
    n = len(differences)
    means = [sum(differences[rng.randrange(n)] for _ in range(n)) / n
             for _ in range(BOOTSTRAPS)]
    return [_percentile(means, 0.025), _percentile(means, 0.975)]


def evaluate_game(game, draws):
    rows = sorted(draws, key=lambda r: int(r["period"]))
    if len(rows) < 60:
        return {"game": game, "error": "该彩种有效历史不足 60 期，无法做可靠时间切分。"}
    test_start = max(40, int(len(rows) * (1.0 - TEST_FRACTION)))
    train_end = test_start
    test_indices = list(range(test_start, len(rows)))
    nn_predictions = _model_scores(game, rows, train_end, test_indices)
    groups = app.GAMES[game]["groups"]
    records = []
    totals = {"nn": 0.0, "bayes": 0.0, "random": 0.0}
    for idx in test_indices:
        row = rows[idx]
        nn_hits = bayes_hits = random_expected = 0.0
        bayes_weights = app.posterior_weights(game, rows[:idx])
        offset = 0
        for gi, (_, maximum, amount, sorted_group) in enumerate(groups):
            if game == "kl8": amount = 20
            actual = row["numbers"]
            if game in ("3d", "pls"):
                for pos in range(amount):
                    nn_pick = _top(nn_predictions[idx][gi][pos], 1)[0]
                    bayes_pick = _top(bayes_weights[gi][pos], 1)[0]
                    nn_hits += nn_pick == actual[pos]
                    bayes_hits += bayes_pick == actual[pos]
                random_expected += amount / maximum
            else:
                actual_set = set(actual[offset:offset + amount])
                nn_pick = set(_top(nn_predictions[idx][gi][0], amount))
                bayes_pick = set(_top(bayes_weights[gi][0], amount))
                nn_hits += len(nn_pick & actual_set)
                bayes_hits += len(bayes_pick & actual_set)
                random_expected += amount * amount / maximum
            offset += groups[gi][2]
        records.append((nn_hits, bayes_hits, random_expected))
        totals["nn"] += nn_hits
        totals["bayes"] += bayes_hits
        totals["random"] += random_expected

    n = len(records)
    nn_diff = [a - c for a, _, c in records]
    bayes_diff = [a - c for _, a, c in records]
    nn_bayes = [a - b for a, b, _ in records]
    ci_random = _ci(nn_diff, 5561)
    ci_bayes = _ci(nn_bayes, 5562)
    group_results = []
    for gi, (label, maximum, amount, _) in enumerate(groups):
        if game == "kl8": amount = 20
        baseline = amount / maximum if game in ("3d", "pls") else amount * amount / maximum
        group_results.append({"label": label, "randomExpected": round(baseline, 4)})
    return {
        "game": game, "drawCount": len(rows), "trainCount": train_end,
        "testCount": n, "trainFirst": rows[0]["period"],
        "trainLast": rows[train_end - 1]["period"],
        "testFirst": rows[test_start]["period"], "testLast": rows[-1]["period"],
        "architecture": f"per-group MLP, 12 hidden units; {WINDOWS[0]}/{WINDOWS[1]} draw features",
        "epochs": EPOCHS, "trainExamplesPerHead": min(MAX_TRAIN, max(0, train_end - 20)),
        "meanHits": {k: round(v / n, 4) for k, v in totals.items()},
        "nnMinusRandom": {"mean": round(statistics.mean(nn_diff), 4),
                          "ci95": [round(x, 4) for x in ci_random]},
        "nnMinusBayes": {"mean": round(statistics.mean(nn_bayes), 4),
                         "ci95": [round(x, 4) for x in ci_bayes]},
        "groups": group_results,
        "beatsRandomAt95": ci_random[0] > 0,
        "beatsBayesAt95": ci_bayes[0] > 0,
        "results": {"random": "显著优于随机" if ci_random[0] > 0 else "未证明显著优于随机",
                    "bayes": "显著优于贝叶斯基线" if ci_bayes[0] > 0 else "未证明显著优于贝叶斯基线"},
        "nextSuggestedNumbers": _next_suggestions(game, rows),
        "forecastNote": "建议号码由全量历史重新训练后生成；回测结论只来自未触及的后 20% 测试期。下一期建议尚未验证。",
        "warning": "这是单次时间留出实验；彩票开奖若独立随机，任何历史优势都可能是噪声，不能保证未来中奖。",
    }


def train_and_backtest(game, draws):
    result = evaluate_game(game, draws)
    if "error" not in result:
        result["trainedAt"] = __import__("datetime").datetime.now().astimezone().isoformat(timespec="seconds")
    return result


def main():
    data = json.loads((Path(__file__).resolve().parent / "draws.json").read_text(encoding="utf-8"))
    results = {game: train_and_backtest(game, rows) for game, rows in data.items() if game in app.GAMES}
    output = Path(__file__).resolve().parent / "neural_backtest_results.json"
    output.write_text(json.dumps(results, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps(results, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
