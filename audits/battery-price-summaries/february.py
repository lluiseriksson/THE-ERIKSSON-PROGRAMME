"""Apply the frozen January comparison to all 672 February hours in NSW1."""
from datetime import datetime
import json
from endpoints import study

if __name__ == '__main__':
    result = study(
        'https://aemo.com.au/aemo/data/nem/priceanddemand/PRICE_AND_DEMAND_202502_NSW1.csv',
        '2fe774a2dc257900ea734278de663dac63b95e5967a5b5e2384aa4d5df17a146',
        datetime(2025, 2, 1), 672)
    print(json.dumps(result, default=str))
