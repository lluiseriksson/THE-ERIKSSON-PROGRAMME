"""Run deterministic certificate checks using only the Python standard library."""
import json
from fractions import Fraction
import verify_donor
import verify_breakpoint
import verify_zero
from verify_observed import verify_observed,need

def main():
    full=verify_donor.verify('full'); restricted=verify_donor.verify('restricted')
    need(full==restricted,'Design diagnostics differ')
    observed=verify_observed();sign=verify_breakpoint.verify();zero=verify_zero.verify()
    need(Fraction(observed['tau_one'])<=Fraction(sign['threshold'])<=Fraction(zero['threshold']),'Nested optima disagree')
    need(zero['zero_attained'],'Equality witness failed')
    print(json.dumps(dict(full=full,observed=observed,sign=sign,zero=zero),sort_keys=True,indent=2))

if __name__=='__main__':main()

