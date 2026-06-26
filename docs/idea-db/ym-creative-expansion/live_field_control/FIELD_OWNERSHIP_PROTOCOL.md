# Field ownership protocol

Each agent owns one field, one proof card, and one mission contract.  It must
return one of:

1. a Lean theorem or theorem-shaped target that removes that exact field;
2. a promoted `source_extracted` record satisfying the source promotion gates;
3. a failed extraction with a narrower, source-located blocker.

Agents must not bundle covariance-root, pushforward, Hessian, activity and H# in
one monolithic theorem package.
