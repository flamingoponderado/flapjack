#!/usr/bin/env python3
"""Regression for every original aligned AMO rd=rs2/rd0/rd=rs1 case.
Pins complete Lean fixture inputs and observation conclusions plus independently
captured original HOL observations. Syntactic check; Lean verifies the replays.
"""
from pathlib import Path
import hashlib
import re
ROOT=Path(__file__).resolve().parents[2]
CASES={
  "amoadd_w_aligned_rd3": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "35241cf3f6717895b3ccd95a131de99d888ae162867cd4618b21164f4a7acb40",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "3d15ead0a374e4e25fa78259822f76694ec2309b5c5f7074ab46aff93bdccce1"
  ],
  "amoadd_w_aligned_rd0": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "e52fb3a05c15687500d7d9518930d05468f7b03a79dd0207533b276bd5d2378d",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "463ff3059645e0181df829cfe675b9d707269634d5e479a99caf2ed317900484"
  ],
  "amoadd_w_aligned_rd2": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "2a8b2b21d0537822af1fa2e0a313f64ad01be79852f754c40eb6b8ccf70e2af8",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "463ff3059645e0181df829cfe675b9d707269634d5e479a99caf2ed317900484"
  ],
  "amoadd_d_aligned_rd3": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "a63ab6b72bf768233041a694a66e4259323b33b6a3e48c23fb8c98d44687cf8f",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "a2d3533279c8d425573b3e7c71352077cf5c7e4b43f25eeb1bcb00ac0e4e7348"
  ],
  "amoadd_d_aligned_rd0": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "8efd2ae23ef91702e90c8a9ec248e369eb0e5cc85f48119a41dee777166828d2",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "fe5596bafa397b1f415534eca8f74af76db2d83d6b6621bdc0fe5e273889129e"
  ],
  "amoadd_d_aligned_rd2": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "cbbae44f8905e153ae869841b8b76ef9d790d87cf9feb226d8507869b0813c8e",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "fe5596bafa397b1f415534eca8f74af76db2d83d6b6621bdc0fe5e273889129e"
  ],
  "amoxor_w_aligned_rd3": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "9d0209784ac40d240622da62282dc5f437b9fc015b8a1e50395b3e49afe851ab",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "4d976448e7c30e849bdc6e960060e672b5f086692805ccb0205a11e7532557de"
  ],
  "amoxor_w_aligned_rd0": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "4c4dad6d9962f5d33ee30ad0ca863b6548d4cde39f21efd34ebfc572893b7cc4",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "88323ee68d2c6f6f0c392ebe70080a2560637d278efce195167d3b2f176bccfb"
  ],
  "amoxor_w_aligned_rd2": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "8756bc19568f23f7530245279b347b8c2e318438169e415c06adb961721c42c4",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "88323ee68d2c6f6f0c392ebe70080a2560637d278efce195167d3b2f176bccfb"
  ],
  "amoxor_d_aligned_rd3": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "05b88da2fc9ac25860185165d231db742ef1b45f84008716336147bdda6680e0",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "75a24a520cece834218961e534f9215c33be05047226b8ca8cac4186538a7158"
  ],
  "amoxor_d_aligned_rd0": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "338d82169b36c665fbf3e381fb8d59fa8a51e1c0fd3cce054da8b9d765b98ab3",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "8f37414d4acd287f409fa616c2d171fc0916176869b797d741b2a7cc9ee5d8f5"
  ],
  "amoxor_d_aligned_rd2": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "015363bd242694db47034288bc2543b4e6084d3c6a8ef21c92f156309d9ca29d",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "8f37414d4acd287f409fa616c2d171fc0916176869b797d741b2a7cc9ee5d8f5"
  ],
  "amoand_w_aligned_rd3": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "fb1929d50c23c032530cd7700e87976c5be7f5c7d845e2d896f5f3c19570c2d4",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "b91e65116a0d216cfd016f2c8303b5863f898a606e736a1e903b2931d4714289"
  ],
  "amoand_w_aligned_rd0": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "2ac6dda24a04abac2800a93dbc693cf3bff0b40915998616e1acdd903bdb389e",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "f21e9a4b50c4e79515df5bad53b74885ef15a2783def34340d7d9de765531b17"
  ],
  "amoand_w_aligned_rd2": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "cf7051aa210e055fc20c4b255fb14045fb4cc803891e3e8addfc21d95a00e7f1",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "f21e9a4b50c4e79515df5bad53b74885ef15a2783def34340d7d9de765531b17"
  ],
  "amoand_d_aligned_rd3": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "41d0dd78ee90c96aef3b875b8cccb0637eaba2cf0b3778e9285c930ac9c50882",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "e0c6065329f7f8da10c8731e10483ff8c5cc78cc40ce295a4f98d8fda6463b18"
  ],
  "amoand_d_aligned_rd0": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "87c65961c5142e1deae3f8b9f642371e301389ca5f22c1c9aae2b43b02915fd7",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "e4b930a4f7f53dc264a75cb25a2e2a82890f05d9a315bfc93be8b43263e37c7c"
  ],
  "amoand_d_aligned_rd2": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "1c348b384cff7e6793ae88f8671b1f4df49494c561d40cb0d3e25885334b04cc",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "e4b930a4f7f53dc264a75cb25a2e2a82890f05d9a315bfc93be8b43263e37c7c"
  ],
  "amoor_w_aligned_rd3": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "1d29b3c9c174c3dccf495dc353d9bd2808f51554cb6352067089e987e03da334",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "856cc12ef58b10b4ea991eb91c3b65f11a66f264f763980c5cd2108736a94f1f"
  ],
  "amoor_w_aligned_rd0": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "4103d97f076c240e45418a7ca0f0a9294e2b8f1fe37d52b305af33ad12a0f3ec",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "e231795793dd0f627224d343caf79c4cd12607eb938f5c8cd06e904a851503ea"
  ],
  "amoor_w_aligned_rd2": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "215a62f86762d28b2b6bce8ce94607627c29356508b1f637eb9325c6f5bd9113",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "e231795793dd0f627224d343caf79c4cd12607eb938f5c8cd06e904a851503ea"
  ],
  "amoor_d_aligned_rd3": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "3dc69204743addb329e97623fcb794a6eb41a5d8a71cfb95e7a68ebcd7641298",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "eec4b8b4ea1fdcab24d1881dc30b81fc33ff20454b1145ee0ff93fa179f1b923"
  ],
  "amoor_d_aligned_rd0": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "d8c5b525592afb837183026f7e9ac8705e19ef8a3672f624daf7755e9369f7fc",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "76b4caa5003517d847a95da7f2930c3a68a37b9da741358bf2402f01576a7eeb"
  ],
  "amoor_d_aligned_rd2": [
    "Flapjack/Test/L3AMOArithmeticParity.lean",
    "4a0bcee9b5b2b32730b2c9b0d8fa7b49c39f3ab80f09e78c01648c7fea5e1348",
    "scripts/hol-probes/l3_amo_arithmetic_probe.out",
    "76b4caa5003517d847a95da7f2930c3a68a37b9da741358bf2402f01576a7eeb"
  ],
  "amomin_w_aligned_rd3": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "a4e6ca3eda4d0d6666a07abc7bd4f8ebbae255d4f6bc6506ecab00ece61bc34e",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "6ac91fea7ef75b7c41ae2afb3ff11756879c5802886021987518eb2e57d135a6"
  ],
  "amomin_w_aligned_rd0": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "039641f0b95ee0d95510e0e2922fee146cf6cfbc79b7f5e60c8587193b04134a",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "3e64091b011dc911732a7ec64eccab5fd7ab2e28a3fc6296de641b7f9377581e"
  ],
  "amomin_w_aligned_rd2": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "36d9b01baf43d9120d8ef18fe2a3c7af2c45d04ecf5a748d02881bb41d9ee545",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "3e64091b011dc911732a7ec64eccab5fd7ab2e28a3fc6296de641b7f9377581e"
  ],
  "amomin_d_aligned_rd3": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "5196813433b472056dcea587b95b923e7342d51be006c22e587aa43957c32b6e",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "8bebf4795edcea62947f1bf244b94e42f7e9a09112c2cf3f4911c28b7bad0efd"
  ],
  "amomin_d_aligned_rd0": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "593cee9d7fa6b136f0f5e5c41ac4049da9ac00be456035a165ebd97658080e57",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "3e64091b011dc911732a7ec64eccab5fd7ab2e28a3fc6296de641b7f9377581e"
  ],
  "amomin_d_aligned_rd2": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "c0a5aa3dd2ee38990b3c6acfc3e115c27bac2c04c0975d054407c81de1af0ec5",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "3e64091b011dc911732a7ec64eccab5fd7ab2e28a3fc6296de641b7f9377581e"
  ],
  "amomax_w_aligned_rd3": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "90621ed8433a8a0984177df00c48691b254aae2b84ac899f8e92f8afa262c0ee",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "9ce233255a7937e12f139df6eb9a2c08a2d825fcea448b543022c0eb3da70dd8"
  ],
  "amomax_w_aligned_rd0": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "d5a9bf99f322a97d849af6f1dedcc9da67e3e2e3760f4b6cb14330051368c751",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "59a42b3605644b7a0f848cd1444265da8d33b511a2b6a048503f04e27058ec3b"
  ],
  "amomax_w_aligned_rd2": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "da958d2efbfcf083d0f39c3b9bb3ed477f2a7666cf4fc64d00b5ce1ea4e41e2b",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "59a42b3605644b7a0f848cd1444265da8d33b511a2b6a048503f04e27058ec3b"
  ],
  "amomax_d_aligned_rd3": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "04d8c75da65498a973e91a51fba42f62c16d7daa4662449ea43e4908bec82c10",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "22f3c8a5da501ebb080d8cf0be2d8987a99077c5fd958951279740c395fb6820"
  ],
  "amomax_d_aligned_rd0": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "030e23c81b01a0253680bbbc0e9291cd4c226870ca0e7ddbf6791e69d170b991",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "93c91478eee1be9d2971f515b0ed0f87211096aa9d7906631809cbec38b53d6b"
  ],
  "amomax_d_aligned_rd2": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "87602dc7ba84f52b3c573d2ae19a31fd02ef98555ad16be98188500c7415cc85",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "93c91478eee1be9d2971f515b0ed0f87211096aa9d7906631809cbec38b53d6b"
  ],
  "amominu_w_aligned_rd3": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "69a4bba9342bd240cb868b0c83db92a9870216d52bee9b79488b63c8bf8fe7f0",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "9ce233255a7937e12f139df6eb9a2c08a2d825fcea448b543022c0eb3da70dd8"
  ],
  "amominu_w_aligned_rd0": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "79424f6e8e04a0ffd270374628636be7a929d05dfb15756b6074d87dc314e05b",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "59a42b3605644b7a0f848cd1444265da8d33b511a2b6a048503f04e27058ec3b"
  ],
  "amominu_w_aligned_rd2": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "934ba06fedd8863e8eabbd3abf439d32cfa1c65ea95e3ca4b3e137093d7215c4",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "59a42b3605644b7a0f848cd1444265da8d33b511a2b6a048503f04e27058ec3b"
  ],
  "amominu_d_aligned_rd3": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "72f1fccb966ad4f963cfcfc83b12ae3fc7dcfae4fe4bb90fd7e0c5ea10648951",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "22f3c8a5da501ebb080d8cf0be2d8987a99077c5fd958951279740c395fb6820"
  ],
  "amominu_d_aligned_rd0": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "06fdfdf1c3bd896c2c6aae69eedb8b748855565356a1d5dafdb59ff24aaf6857",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "93c91478eee1be9d2971f515b0ed0f87211096aa9d7906631809cbec38b53d6b"
  ],
  "amominu_d_aligned_rd2": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "b6b360c4884b6626197ba3752ebfd334ffef8f024129d0a84ce3c40be6b86a74",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "93c91478eee1be9d2971f515b0ed0f87211096aa9d7906631809cbec38b53d6b"
  ],
  "amomaxu_w_aligned_rd3": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "c6b107e11d4ab3e74050a0f777577b8c2814368c16905cb5055f0a1d5353e307",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "6ac91fea7ef75b7c41ae2afb3ff11756879c5802886021987518eb2e57d135a6"
  ],
  "amomaxu_w_aligned_rd0": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "534828b7640e2f150794efcaebffc3ea4f3be0f8f12f2d2f1ebc3a8979c4f0e8",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "3e64091b011dc911732a7ec64eccab5fd7ab2e28a3fc6296de641b7f9377581e"
  ],
  "amomaxu_w_aligned_rd2": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "d1885c5241aa1ea543dffca87b4570ac9ae9752774d5f004f4bb6f930b364662",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "3e64091b011dc911732a7ec64eccab5fd7ab2e28a3fc6296de641b7f9377581e"
  ],
  "amomaxu_d_aligned_rd3": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "074d41f8298dcc8028fedc4ff623836c9a4566b89c73c8611f7a5ca593ef696a",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "8bebf4795edcea62947f1bf244b94e42f7e9a09112c2cf3f4911c28b7bad0efd"
  ],
  "amomaxu_d_aligned_rd0": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "1fe7663d09dcdb237dbb95c52739e322d2342598cbf968873f8e64289d4de162",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "3e64091b011dc911732a7ec64eccab5fd7ab2e28a3fc6296de641b7f9377581e"
  ],
  "amomaxu_d_aligned_rd2": [
    "Flapjack/Test/L3AMOMinMaxParity.lean",
    "024be36ffbc817ddcf44c06c3136143f0034e60ceeba4f0a8de9c1675ffdb1da",
    "scripts/hol-probes/l3_amo_minmax_probe.out",
    "3e64091b011dc911732a7ec64eccab5fd7ab2e28a3fc6296de641b7f9377581e"
  ]
}
def check(root=ROOT):
    for label,(lean,statement_hash,oracle,oracle_hash) in CASES.items():
        text=(root/lean).read_text()
        blocks=[m.group(0).split(' := by',1)[0] for m in re.finditer(r'^-- Original (\S+);.*?(?=^-- Original |^end Flapjack.Test.)',text,re.M|re.S) if m.group(1)==label]
        if len(blocks)!=1 or hashlib.sha256(blocks[0].encode()).hexdigest()!=statement_hash:
            raise ValueError('missing/changed original AMO alias case: '+label)
        rows=[line.split('=',1)[1] for line in (root/oracle).read_text().splitlines() if line.startswith(label+'=')]
        if len(rows)!=1 or hashlib.sha256(rows[0].encode()).hexdigest()!=oracle_hash:
            raise ValueError('missing/changed independent HOL AMO alias row: '+label)
    for family,count in [('Arithmetic',86),('MinMax',134)]:
        if (root/f'Flapjack/Test/L3AMO{family}Parity.lean').read_text().count('\nexample ')!=count:
            raise ValueError('retained AMO replay count drift: '+family)
    return True
if __name__=='__main__':
    check()
    print('48 distinct original aligned AMO register alias replays PASS')
