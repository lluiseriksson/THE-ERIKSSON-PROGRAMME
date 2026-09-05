"""Draft exact audit gate for steps 14/15; no Lean or subprocess invocation.

Not installed in a runner. Test in Colab before using for a seal. In
particular, a proposition-valued certificate projection may have no axioms.
The empty case must not be confused with a missing/truncated audit block.
"""
import re

ALLOWED = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
BLOCK = re.compile(
    r"'([^']+)'(?:dependsonaxioms:\[([^\]]*)\]|doesnotdependonanyaxioms)"
)


def exact_axioms(output, expected):
    compact = re.sub(r'\s+', '', output)
    if any(word in compact for word in ('sorryAx', 'ofReduceBool')):
        raise ValueError('FORBIDDEN_AXIOM')
    blocks = list(BLOCK.finditer(compact))
    names = [block.group(1) for block in blocks]
    if len(names) != len(expected) or set(names) != set(expected):
        raise ValueError('AXIOM_DECLARATIONS_MISMATCH')
    result = {}
    for block in blocks:
        name, body = block.groups()
        axioms = [] if body is None or body == '' else body.split(',')
        if any(not item or item not in ALLOWED for item in axioms):
            raise ValueError('UNAPPROVED_OR_MALFORMED_AXIOM=' + name)
        if len(axioms) != len(set(axioms)):
            raise ValueError('DUPLICATE_AXIOM=' + name)
        result[name] = sorted(axioms)
    # An extra malformed/truncated header is not invisible just because it
    # failed to match a complete block above.
    remainder = BLOCK.sub('', compact)
    if 'dependsonaxioms' in remainder or 'doesnotdependonanyaxioms' in remainder:
        raise ValueError('UNPARSED_AXIOM_HEADER')
    return result


def self_test():
    full = "'full' depends on axioms: [propext,\nClassical.choice, Quot.sound]"
    pure = "'pure' does not depend on any axioms"
    sample = full + '\n' + pure
    expected = {'full', 'pure'}
    assert exact_axioms(sample, expected) == {
        'full': sorted(ALLOWED), 'pure': []}
    assert exact_axioms("'pure' depends on axioms: []", {'pure'}) == {'pure': []}
    bad = [
        full, sample + '\n' + pure,
        sample.replace("'pure'", "'wrong'"),
        sample.replace('Quot.sound', 'sorryAx'),
        sample.replace('Quot.sound', 'ofReduceBool'),
        sample.replace('Quot.sound', 'Other.axiom'),
        sample.replace('Quot.sound', ''),
        sample.replace('Quot.sound', 'propext'),
        sample + "\n'extra' depends on axioms: [",
    ]
    for item in bad:
        try:
            exact_axioms(item, expected)
        except ValueError:
            continue
        raise AssertionError('REJECTION_SELF_TEST_FAILED')
    print('OWNER_AXIOM_GATE_SELF_TEST=PASS valid=2 rejected=' + str(len(bad)))


if __name__ == '__main__':
    self_test()
