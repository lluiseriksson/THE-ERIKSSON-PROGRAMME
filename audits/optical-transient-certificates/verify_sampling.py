"""Exact arithmetic for the optical sampling example and stability margin."""
from fractions import Fraction as F
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def intensity(a):
    return (11 - 20 * a) ** 2 + 904


def verify(grid):
    raw = [intensity(a) for a in grid]
    mean = (raw[0] + raw[-1]) / 2
    critical = F(11, 20)
    sampled = min(raw)
    require(critical not in grid and min(grid) == 0 and max(grid) == 1, 'Unexpected grid')
    require([a for a in grid if intensity(a) == sampled] == [F(1, 2), F(3, 5)], 'Wrong nearest samples')
    require(mean == 1005 and sampled == 905 and intensity(critical) == 904, 'Intensity mismatch')
    threshold = F(9, 10) * mean
    change = 2 * 43**2 * F(1, 10000)
    require(intensity(critical) + change < threshold < sampled - change, 'Moving witness fails')
    normalized_curvature = 2 * F(20, 43)**2
    gap = (sampled - intensity(critical)) / 43**2
    require(gap == normalized_curvature * F(1, 10)**2 / 8, 'Curvature sharpness fails')
    h = lambda t: 10*t**3 - 15*t**4 + 6*t**5
    require(h(F(1,4)) / h(F(1,2)) == F(53,256), 'Quintic readout differs')
    return dict(grid_min=str(sampled / mean), continuous_min=str(intensity(critical) / mean),
                frame_mean=str(mean), worst_time=str(critical), curvature_gap=str(gap),
                moving_grid_lower=str((sampled-change)/mean), moving_continuous_upper=str((intensity(critical)+change)/mean))


grid = [F(j, 10) for j in range(11)]
result = verify(grid)
try:
    verify(sorted(grid+[F(11, 20)]))
except ValueError:
    result['extra_midcell_sample_detected'] = True
else:
    raise RuntimeError('Failed to detect altered grid')
print(json.dumps(result, sort_keys=True, indent=2))

