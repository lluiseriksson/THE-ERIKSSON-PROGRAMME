# Weight sensitivity of leadership in the CAIDP AI Index

The manuscript compares two public editions of the Center for AI and Digital Policy index. The boundary is a property of the scores assigned by the publisher. The script computes it with exact fractions and checks each boundary witness against the entire comparison group.

Use Python 3 and run `python reproduce.py` in the sanctioned Linux runtime. To reproduce offline after obtaining the referenced unmodified bundle, use `python reproduce.py --bundle PATH`. A changed download fails the checksum. No third-party JavaScript executes. See the publisher's 2025 and 2026 release pages for the underlying copyrighted works. Those works are not redistributed here.

The output reports the whole-edition threshold and all four combinations of leader and challenger ratings among the 80 shared countries. All rankings use the numerical score. The five published tiers are distinct categories.

Sources: https://www.caidp.org/reports/caidp-index-2025/ and https://www.caidp.org/reports/caidp-index-2026/ .
