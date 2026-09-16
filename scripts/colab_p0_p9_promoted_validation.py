#!/usr/bin/env python3
"""Generated fresh-clone gate for the promoted P0--P9 tracked graph."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import urllib.request

SOURCE_SHA = '10e6899692defec09b416d73a64ec36ee5cc7393'
RUNNER_REV = 'p0-p9-promoted-10e6899692de-v1'
BASE_RUNNER_URL = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/bcc852cee5e709bff91fad7de26fa21cff754e1f/scripts/colab_qprime_row_validation.py'
BASE_RUNNER_SHA256 = 'd06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee'
BASE_RUNNER = Path("/content/colab_qprime_row_validation.py")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP85BlockGaussianAlgebra.lean": "30891b3beb49fb28535de361f1c857d44223dd3d0b44d5e3d710a8052a0a8c44",
    "YangMills/RG/BalabanCMP85BlockGaussianAlgebraAudit.lean": "3a592639ca3c8da753370a054462bf7399898bb15a0e98418546250ad6159100",
    "YangMills/RG/BalabanCMP85Eq221EffectiveQuadratic.lean": "f58fee6e3b7772b713cca9737ac6647562a049ab0a9b79e6b68084d73c2c953b",
    "YangMills/RG/BalabanCMP85Eq221EffectiveQuadraticAudit.lean": "da4c46d67e53c469ebada8637a6c0ecc5d20c97aa57636b55ea9a47f556bc80c",
    "YangMills/RG/BalabanCMP85Eq230BaseCovariance.lean": "0b1e2bbf08bc1445717ce927f7b96d3ad8c2ab0c4326f3b651d610fd32b3bd14",
    "YangMills/RG/BalabanCMP85Eq230BaseCovarianceAudit.lean": "49b159f61135c748cac86039bb334a6d5be3c0496d7d1af83a7675656958a26d",
    "YangMills/RG/BalabanCMP85Eq230CoarseCovariance.lean": "a56bef31cf55df8c02bda2e4b2a739ff53335ee77b8f02ce601662464f476f27",
    "YangMills/RG/BalabanCMP85Eq230CoarseCovarianceAudit.lean": "70d850237c547d31122dcb4ca57f72f500222d473800052f44be8ba6faa40aa0",
    "YangMills/RG/BalabanCMP85Eq241Eq242PhysicalGreenRecurrence.lean": "0292667a4814002c38c062a8588cc385fd0b61904c61d17e18af20841fe4530d",
    "YangMills/RG/BalabanCMP85Eq241Eq242PhysicalGreenRecurrenceAggregateAudit.lean": "a274ad6c3273f639bb2dd28a0c8230e409b8452c0f61ca45f9f999f4140539d6",
    "YangMills/RG/BalabanCMP85Eq241Eq242PhysicalGreenRecurrenceAudit.lean": "9ad1c82b94c7a5e772b2439769231ffe03510589f1fdee6d37e3ba1111a18bdf",
    "YangMills/RG/BalabanCMP85Eq243PhysicalGreenScaleSum.lean": "bef1488461ec4e8d89bc7ec880cf549755e03f365adcc4922ddc2cc03603d5d6",
    "YangMills/RG/BalabanCMP85Eq243PhysicalGreenScaleSumAudit.lean": "55984c8ef67556c46dcfae798c69985f043e6a5f30e9cb4ec58f81274993e4a5",
    "YangMills/RG/BalabanCMP85PhysicalOperatorDictionary.lean": "812cc8e2689a1f40ca0510e418a99164da5ff300992c1fdc262cce7da119aeff",
    "YangMills/RG/BalabanCMP85PhysicalOperatorDictionaryAudit.lean": "8f368a7d33956f5d0a1848aa2bc67cda91b7b252253058a65134807379c8a428",
    "YangMills/RG/BalabanCMP85PhysicalScalarSpecialization.lean": "39203401de560ec8f0535c894c60510f0d05ed0181e96b5f90419a4d7b9529d2",
    "YangMills/RG/BalabanCMP85PhysicalScalarSpecializationAudit.lean": "d906f425c457af9fa236fbedbe8546fee8368231b368d24643256c038aa3aaeb",
    "YangMills/RG/BalabanCMP85ScalarRecurrence.lean": "8cf31a15160ea38b093ed821a4c20b0a0038c0cad07381a37709b6eea161df64",
    "YangMills/RG/BalabanCMP85ScalarRecurrenceAudit.lean": "73c58dbbf4df17afd650b11c1c947a6bed863be1ab750e2e6ada06ea6cb99e32",
    "YangMills/RG/BalabanCMP85SourcePrefixGreen.lean": "81aefbe7d79c15904a223a25d2e728152ec7539ba43197decbea195b802f8015",
    "YangMills/RG/BalabanCMP85SourcePrefixGreenAudit.lean": "682f836ef2adadbf0ff548311bc9444494576bdaf5a6112489ef506deeb262db",
    "YangMills/RG/BalabanCMP85SourceStepCoisometry.lean": "c698846816c132c0c66f4350949ca2c48aa6dde2fdb817d00d9e8eaebd905e11",
    "YangMills/RG/BalabanCMP85SourceStepCoisometryAudit.lean": "bc2616515afb91d8d849b88758da8aa015570dbab2b1234fe1f6d9641415115c",
    "YangMills/RG/BalabanCMP85TypedGreenInverse.lean": "2bb7688ce0d94ded074bfb2ef7e514951f30d5bab963da441e3d4c50444c2033",
    "YangMills/RG/BalabanCMP85TypedGreenInverseAudit.lean": "248ebeaa5033f2c869a454ec8e1e95b54fbbfb349fee39a3443f530f33d9cae0",
    "YangMills/RG/BalabanCMP85TypedSchurBrackets.lean": "bb80e30f8e1e09e6507241863c54d44fe11666b28b136be70828f88c34000785",
    "YangMills/RG/BalabanCMP85TypedSchurBracketsAudit.lean": "6732fcd5d6d901a8d5b16923289c64850b20c4073905fe4e229d13fafaef9bff",
    "YangMills/RG/BalabanCMP89Eq234PhysicalGreenScaleDictionary.lean": "0bf77fb90d3d923a178ed46c2d9703a2f07cb24050030d85e5dfed0469034c0e",
    "YangMills/RG/BalabanCMP89Eq234PhysicalGreenScaleDictionaryAudit.lean": "097caf68eedc70785cc4a1d6b320c4bfd31a22f9414099ff201dda652c6e24f5",
    "YangMills/RG/BalabanCMP89SourceSeparatedAmbientPrefixPrecision.lean": "8163640c7372830aaa3196845a34f40eaca9a8ba03593bd913b3262c2b53df8d",
    "YangMills/RG/BalabanCMP89SourceSeparatedAmbientPrefixPrecisionAudit.lean": "4f004a799cb5100ee4e755fd654735a804d7a0ea69c75eecaff79d2b6ffcf843",
    "YangMills/RG/BalabanCMP89SourceSeparatedPrefixCombesThomas.lean": "2e138ed8d3f6f635d410711354625d93783b649b2504e5c28349ae004ec2a211",
    "YangMills/RG/BalabanCMP89SourceSeparatedPrefixCombesThomasAudit.lean": "f628fa682ee43e535d530953514edb0d87ba63af68d808ba43d072adf2d1d926",
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixGreen.lean": "441587b5de4dd3ee8dd23962e71ed4c8424b29f860ad44b17df4892297af13a8",
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixGreenAudit.lean": "f736eadbc0e52d7fb2c5aae8a5a13d319432ac931d0780dbbb8b2ed0c252e554",
    "YangMills/RG/BalabanCMP99SourceCanonicalPrefixTower.lean": "1f3b3a7933441e39715d9c72336111d80e7aaf190f1c4fcdc9f9fe7015c1a91d",
    "YangMills/RG/BalabanCMP99SourceCanonicalPrefixTowerAudit.lean": "fbd043ec950477a88c71c1601d991e0271d47fd2d1ea9e09125239e2c263efc5",
    "YangMills/RG/BalabanCMP99SourcePrefixPoincare.lean": "548609c4f0cde8e0cfd3d91e2acb5dfae1b61c8cd533c8756f5fc4a5eb26bafc",
    "YangMills/RG/BalabanCMP99SourcePrefixPoincareAudit.lean": "5544d89773a94a3a2a233dda4e236a88eaeaed0dac917d0a54c303271a9dc523"
}
QUEUE = [('p0_p9_promoted_materialize_project_prerequisites', ['lake', 'build', 'YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge', 'YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance', 'YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary', 'YangMills.RG.FinitePiLpTypedKernelReindexAlgebra'], None), ('p0_p9_promoted_prepare_build_dirs', ['mkdir', '-p', '.lake/build/lib/lean/YangMills/RG'], None), ('p0_p9_promoted_01_balabancmp99sourcecanonicalprefixtower', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99SourceCanonicalPrefixTower.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP99SourceCanonicalPrefixTower.olean'], None), ('p0_p9_promoted_02_balabancmp99sourcecanonicalprefixtoweraudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99SourceCanonicalPrefixTowerAudit.lean'], 10), ('p0_p9_promoted_03_balabancmp99sourceprefixpoincare', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99SourcePrefixPoincare.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP99SourcePrefixPoincare.olean'], None), ('p0_p9_promoted_04_balabancmp99sourceprefixpoincareaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99SourcePrefixPoincareAudit.lean'], 8), ('p0_p9_promoted_05_balabancmp85sourceprefixgreen', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85SourcePrefixGreen.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85SourcePrefixGreen.olean'], None), ('p0_p9_promoted_06_balabancmp85sourceprefixgreenaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85SourcePrefixGreenAudit.lean'], 26), ('p0_p9_promoted_07_balabancmp85eq221effectivequadratic', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85Eq221EffectiveQuadratic.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85Eq221EffectiveQuadratic.olean'], None), ('p0_p9_promoted_08_balabancmp85eq221effectivequadraticaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85Eq221EffectiveQuadraticAudit.lean'], 10), ('p0_p9_promoted_09_balabancmp85eq230coarsecovariance', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85Eq230CoarseCovariance.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85Eq230CoarseCovariance.olean'], None), ('p0_p9_promoted_10_balabancmp85eq230coarsecovarianceaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85Eq230CoarseCovarianceAudit.lean'], 24), ('p0_p9_promoted_11_balabancmp85scalarrecurrence', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85ScalarRecurrence.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85ScalarRecurrence.olean'], None), ('p0_p9_promoted_12_balabancmp85scalarrecurrenceaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85ScalarRecurrenceAudit.lean'], 9), ('p0_p9_promoted_13_balabancmp85blockgaussianalgebra', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85BlockGaussianAlgebra.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85BlockGaussianAlgebra.olean'], None), ('p0_p9_promoted_14_balabancmp85blockgaussianalgebraaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85BlockGaussianAlgebraAudit.lean'], 2), ('p0_p9_promoted_15_balabancmp85typedschurbrackets', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85TypedSchurBrackets.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85TypedSchurBrackets.olean'], None), ('p0_p9_promoted_16_balabancmp85typedschurbracketsaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85TypedSchurBracketsAudit.lean'], 8), ('p0_p9_promoted_17_balabancmp85typedgreeninverse', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85TypedGreenInverse.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85TypedGreenInverse.olean'], None), ('p0_p9_promoted_18_balabancmp85typedgreeninverseaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85TypedGreenInverseAudit.lean'], 8), ('p0_p9_promoted_19_balabancmp85sourcestepcoisometry', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85SourceStepCoisometry.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85SourceStepCoisometry.olean'], None), ('p0_p9_promoted_20_balabancmp85sourcestepcoisometryaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85SourceStepCoisometryAudit.lean'], 2), ('p0_p9_promoted_21_balabancmp85physicalscalarspecialization', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85PhysicalScalarSpecialization.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85PhysicalScalarSpecialization.olean'], None), ('p0_p9_promoted_22_balabancmp85physicalscalarspecializationaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85PhysicalScalarSpecializationAudit.lean'], 4), ('p0_p9_promoted_23_balabancmp85physicaloperatordictionary', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85PhysicalOperatorDictionary.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85PhysicalOperatorDictionary.olean'], None), ('p0_p9_promoted_24_balabancmp85physicaloperatordictionaryaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85PhysicalOperatorDictionaryAudit.lean'], 3), ('p0_p9_promoted_25_balabancmp85eq241eq242physicalgreenrecurrence', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85Eq241Eq242PhysicalGreenRecurrence.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85Eq241Eq242PhysicalGreenRecurrence.olean'], None), ('p0_p9_promoted_26_balabancmp85eq241eq242physicalgreenrecurrenceaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85Eq241Eq242PhysicalGreenRecurrenceAudit.lean'], 3), ('p0_p9_promoted_27_balabancmp85eq241eq242physicalgreenrecurrenceaggregateaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85Eq241Eq242PhysicalGreenRecurrenceAggregateAudit.lean'], 18), ('p0_p9_promoted_28_balabancmp85eq230basecovariance', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85Eq230BaseCovariance.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85Eq230BaseCovariance.olean'], None), ('p0_p9_promoted_29_balabancmp85eq230basecovarianceaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85Eq230BaseCovarianceAudit.lean'], 12), ('p0_p9_promoted_30_balabancmp85eq243physicalgreenscalesum', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85Eq243PhysicalGreenScaleSum.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP85Eq243PhysicalGreenScaleSum.olean'], None), ('p0_p9_promoted_31_balabancmp85eq243physicalgreenscalesumaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP85Eq243PhysicalGreenScaleSumAudit.lean'], 14), ('p0_p9_promoted_32_balabancmp89eq234physicalgreenscaledictionary', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89Eq234PhysicalGreenScaleDictionary.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP89Eq234PhysicalGreenScaleDictionary.olean'], None), ('p0_p9_promoted_33_balabancmp89eq234physicalgreenscaledictionaryaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89Eq234PhysicalGreenScaleDictionaryAudit.lean'], 14), ('p0_p9_promoted_materialize_p7_p9_project_prerequisites', ['lake', 'build', 'YangMills.RG.BalabanCMP99SourceGeneratedPhysicalAmbientDictionary', 'YangMills.RG.BalabanCMP99SourceGeneratedRegionalFinePartition', 'YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition', 'YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas', 'YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay'], None), ('p0_p9_promoted_34_balabancmp89sourceseparatedambientprefixprecision', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89SourceSeparatedAmbientPrefixPrecision.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP89SourceSeparatedAmbientPrefixPrecision.olean'], None), ('p0_p9_promoted_35_balabancmp89sourceseparatedambientprefixprecisionaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89SourceSeparatedAmbientPrefixPrecisionAudit.lean'], 8), ('p0_p9_promoted_36_balabancmp96sourceseparatedregionalprefixgreen', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixGreen.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixGreen.olean'], None), ('p0_p9_promoted_37_balabancmp96sourceseparatedregionalprefixgreenaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixGreenAudit.lean'], 5), ('p0_p9_promoted_38_balabancmp89sourceseparatedprefixcombesthomas', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89SourceSeparatedPrefixCombesThomas.lean', '-o', '.lake/build/lib/lean/YangMills/RG/BalabanCMP89SourceSeparatedPrefixCombesThomas.olean'], None), ('p0_p9_promoted_39_balabancmp89sourceseparatedprefixcombesthomasaudit', ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89SourceSeparatedPrefixCombesThomasAudit.lean'], 12)]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def fetch_exact(url: str, expected: str) -> bytes:
    with urllib.request.urlopen(url) as response:
        payload = response.read()
    measured = hashlib.sha256(payload).hexdigest()
    print("BASE_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
    if measured != expected:
        raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
    return payload


BASE_RUNNER.write_bytes(fetch_exact(BASE_RUNNER_URL, BASE_RUNNER_SHA256))
spec = importlib.util.spec_from_file_location("promoted_base_runner", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load exact base runner")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def parse_axioms(output: str, expected: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != expected:
        raise RuntimeError(
            f"AXIOM_HEADER_COUNT={len(blocks) + pure} EXPECTED={expected}"
        )
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"AXIOM_SET_{index}={sorted(names)}")


runner.RUNNER_REV = RUNNER_REV
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-p0-p9-promoted")
runner.EVIDENCE = Path("/content/hrpoly-p0-p9-promoted-evidence")
runner.ARCHIVE = Path("/content/hrpoly-p0-p9-promoted-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-p0-p9-promoted-paths.txt")
runner.SOURCE_BLOBS = SOURCE_BLOBS
runner.QUEUE = QUEUE
runner.parse_axioms = parse_axioms


if __name__ == "__main__":
    try:
        from google.colab import runtime
        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    code = runner.main()
    try:
        from google.colab import files
        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    raise SystemExit(code)
