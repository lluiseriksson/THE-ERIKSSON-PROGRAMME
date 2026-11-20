"""Reproduce monthly leader bounds from aggregated month-by-dataset counts."""
from collections import Counter
from pathlib import Path
import json
import sys


def month_bounds(counts):
    """Months compatible with joint first, and months guaranteed strictly first."""
    if not sum(counts.values()):
        return [], []
    unknown = counts.get("unknown", 0)
    months = {i: counts.get(str(i), 0) for i in range(1, 13)}
    possible = [i for i, count in months.items() if count + unknown >= max(months.values())]
    certain = [
        i for i, count in months.items()
        if count > max(other for j, other in months.items() if j != i) + unknown
    ]
    return possible, certain


def summarize(datasets):
    totals = sum((Counter(months) for months in datasets.values()), Counter())
    complete = month_bounds(totals)
    omissions = {key: month_bounds(totals - Counter(months)) for key, months in datasets.items()}
    return {"all_records": complete, "omit_one_dataset": omissions}


if __name__ == "__main__":
    source = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name("monthly-counts.json")
    panel = json.loads(source.read_text(encoding="utf-8"))
    print(json.dumps({taxon: summarize(rows["datasets"]) for taxon, rows in panel.items()
                      if "datasets" in rows}, indent=2))

