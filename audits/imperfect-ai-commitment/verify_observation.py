from fractions import Fraction as F
import json
from pathlib import Path
panel=json.loads(Path('pooling.json').read_bytes())['pooling']
mix=json.loads(Path('mixture.json').read_bytes())
if not (panel['cases']==197 and 0<panel['coexist']<panel['cases'] and panel['on_k']>0 and panel['on_c']>0):raise ValueError('Panel counts')
x=F(mix['share']);rho=F(mix['observation']);m=F(mix['theta_adoption']);y=F(mix['population_adoption'])
if not (y==x*m==4-6*x and 0<y<F(1,2) and F(mix['fitness_gap'])==-F(9,10)):raise ValueError('Witness')
if F(mix['utility_when_committed'])!=F(mix['utility_when_discretionary']) or F(mix['selfish_utility'])<=F(mix['selfish_deviation']):raise ValueError('Incentives')
if -F(mix['fitness_gap'])<y/3:raise ValueError('Gap bound')
print('Pooling panel, interior mixed equilibrium and material bound checked.')
