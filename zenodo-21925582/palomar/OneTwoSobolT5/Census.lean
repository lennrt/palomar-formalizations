/-
Paper: Exact Projection Quality of OneTwo Sobol' Sequences at 65,536 Points
Paper author: Lennart Rudolph, the sole author of record on the Zenodo deposit
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925582
Formalization: Lennart Rudolph, the responsible author, with the automated
assistants Sol (OpenAI Codex) and Fable (Anthropic Claude)
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import OneTwoSobolT5.Census.Windows00
import OneTwoSobolT5.Census.Windows01
import OneTwoSobolT5.Census.Windows02
import OneTwoSobolT5.Census.Windows03
import OneTwoSobolT5.Census.Windows04
import OneTwoSobolT5.Census.Windows05
import OneTwoSobolT5.Census.Windows06
import OneTwoSobolT5.Census.Windows07
import OneTwoSobolT5.Census.Windows08
import OneTwoSobolT5.Census.Windows09
import OneTwoSobolT5.Census.Windows10
import OneTwoSobolT5.Census.Windows11
import OneTwoSobolT5.Census.Windows12
import OneTwoSobolT5.Census.Windows13
import OneTwoSobolT5.Census.Windows14
import OneTwoSobolT5.Census.Windows15
import OneTwoSobolT5.Census.Windows16
import OneTwoSobolT5.Census.Windows17
import OneTwoSobolT5.Census.Windows18
import OneTwoSobolT5.Census.Windows19
import OneTwoSobolT5.Census.Windows20
import OneTwoSobolT5.Census.Windows21
import OneTwoSobolT5.Census.Windows22
import OneTwoSobolT5.Census.Windows23
import OneTwoSobolT5.Census.Windows24
import OneTwoSobolT5.Census.Windows25
import OneTwoSobolT5.Census.Windows26
import OneTwoSobolT5.Census.Windows27
import OneTwoSobolT5.Census.Windows28
import OneTwoSobolT5.Census.Windows29
import OneTwoSobolT5.Census.Windows30
import OneTwoSobolT5.Census.Windows31
import OneTwoSobolT5.Census.Windows32
import OneTwoSobolT5.Census.Windows33
import OneTwoSobolT5.Census.Windows34

/-!
# The complete pair-aligned window census

The advertised census theorem quantifies over `buildWindows allRows
censusTs`, so its meaning is pinned entirely by the master dimension table
and the claimed quality parameters.  Each `wN_ok` row-reduction check lives
in one of the 35 window shard files; this file only assembles them.
-/

namespace OneTwoSobolT5.Census

set_option maxHeartbeats 0
set_option maxRecDepth 400000

/-- The 345 windows, written out. -/
def wlist : List Window := [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80, w81, w82, w83, w84, w85, w86, w87, w88, w89, w90, w91, w92, w93, w94, w95, w96, w97, w98, w99, w100, w101, w102, w103, w104, w105, w106, w107, w108, w109, w110, w111, w112, w113, w114, w115, w116, w117, w118, w119, w120, w121, w122, w123, w124, w125, w126, w127, w128, w129, w130, w131, w132, w133, w134, w135, w136, w137, w138, w139, w140, w141, w142, w143, w144, w145, w146, w147, w148, w149, w150, w151, w152, w153, w154, w155, w156, w157, w158, w159, w160, w161, w162, w163, w164, w165, w166, w167, w168, w169, w170, w171, w172, w173, w174, w175, w176, w177, w178, w179, w180, w181, w182, w183, w184, w185, w186, w187, w188, w189, w190, w191, w192, w193, w194, w195, w196, w197, w198, w199, w200, w201, w202, w203, w204, w205, w206, w207, w208, w209, w210, w211, w212, w213, w214, w215, w216, w217, w218, w219, w220, w221, w222, w223, w224, w225, w226, w227, w228, w229, w230, w231, w232, w233, w234, w235, w236, w237, w238, w239, w240, w241, w242, w243, w244, w245, w246, w247, w248, w249, w250, w251, w252, w253, w254, w255, w256, w257, w258, w259, w260, w261, w262, w263, w264, w265, w266, w267, w268, w269, w270, w271, w272, w273, w274, w275, w276, w277, w278, w279, w280, w281, w282, w283, w284, w285, w286, w287, w288, w289, w290, w291, w292, w293, w294, w295, w296, w297, w298, w299, w300, w301, w302, w303, w304, w305, w306, w307, w308, w309, w310, w311, w312, w313, w314, w315, w316, w317, w318, w319, w320, w321, w322, w323, w324, w325, w326, w327, w328, w329, w330, w331, w332, w333, w334, w335, w336, w337, w338, w339, w340, w341, w342, w343, w344]

/-- The table-built windows are exactly the 345 written-out windows. -/
theorem buildWindows_eq_wlist : buildWindows allRows censusTs = wlist := by
  decide

/-- Every written-out window passes its rank-profile check. -/
theorem wlist_all : wlist.all (fun w => windowExactT w) = true := by
  simp only [wlist, List.all_cons, List.all_nil, Bool.true_and,
    w0_ok, w1_ok, w2_ok, w3_ok, w4_ok, w5_ok, w6_ok, w7_ok, w8_ok, w9_ok,
    w10_ok, w11_ok, w12_ok, w13_ok, w14_ok, w15_ok, w16_ok, w17_ok, w18_ok,
    w19_ok, w20_ok, w21_ok, w22_ok, w23_ok, w24_ok, w25_ok, w26_ok, w27_ok,
    w28_ok, w29_ok, w30_ok, w31_ok, w32_ok, w33_ok, w34_ok, w35_ok, w36_ok,
    w37_ok, w38_ok, w39_ok, w40_ok, w41_ok, w42_ok, w43_ok, w44_ok, w45_ok,
    w46_ok, w47_ok, w48_ok, w49_ok, w50_ok, w51_ok, w52_ok, w53_ok, w54_ok,
    w55_ok, w56_ok, w57_ok, w58_ok, w59_ok, w60_ok, w61_ok, w62_ok, w63_ok,
    w64_ok, w65_ok, w66_ok, w67_ok, w68_ok, w69_ok, w70_ok, w71_ok, w72_ok,
    w73_ok, w74_ok, w75_ok, w76_ok, w77_ok, w78_ok, w79_ok, w80_ok, w81_ok,
    w82_ok, w83_ok, w84_ok, w85_ok, w86_ok, w87_ok, w88_ok, w89_ok, w90_ok,
    w91_ok, w92_ok, w93_ok, w94_ok, w95_ok, w96_ok, w97_ok, w98_ok, w99_ok,
    w100_ok, w101_ok, w102_ok, w103_ok, w104_ok, w105_ok, w106_ok, w107_ok,
    w108_ok, w109_ok, w110_ok, w111_ok, w112_ok, w113_ok, w114_ok, w115_ok,
    w116_ok, w117_ok, w118_ok, w119_ok, w120_ok, w121_ok, w122_ok, w123_ok,
    w124_ok, w125_ok, w126_ok, w127_ok, w128_ok, w129_ok, w130_ok, w131_ok,
    w132_ok, w133_ok, w134_ok, w135_ok, w136_ok, w137_ok, w138_ok, w139_ok,
    w140_ok, w141_ok, w142_ok, w143_ok, w144_ok, w145_ok, w146_ok, w147_ok,
    w148_ok, w149_ok, w150_ok, w151_ok, w152_ok, w153_ok, w154_ok, w155_ok,
    w156_ok, w157_ok, w158_ok, w159_ok, w160_ok, w161_ok, w162_ok, w163_ok,
    w164_ok, w165_ok, w166_ok, w167_ok, w168_ok, w169_ok, w170_ok, w171_ok,
    w172_ok, w173_ok, w174_ok, w175_ok, w176_ok, w177_ok, w178_ok, w179_ok,
    w180_ok, w181_ok, w182_ok, w183_ok, w184_ok, w185_ok, w186_ok, w187_ok,
    w188_ok, w189_ok, w190_ok, w191_ok, w192_ok, w193_ok, w194_ok, w195_ok,
    w196_ok, w197_ok, w198_ok, w199_ok, w200_ok, w201_ok, w202_ok, w203_ok,
    w204_ok, w205_ok, w206_ok, w207_ok, w208_ok, w209_ok, w210_ok, w211_ok,
    w212_ok, w213_ok, w214_ok, w215_ok, w216_ok, w217_ok, w218_ok, w219_ok,
    w220_ok, w221_ok, w222_ok, w223_ok, w224_ok, w225_ok, w226_ok, w227_ok,
    w228_ok, w229_ok, w230_ok, w231_ok, w232_ok, w233_ok, w234_ok, w235_ok,
    w236_ok, w237_ok, w238_ok, w239_ok, w240_ok, w241_ok, w242_ok, w243_ok,
    w244_ok, w245_ok, w246_ok, w247_ok, w248_ok, w249_ok, w250_ok, w251_ok,
    w252_ok, w253_ok, w254_ok, w255_ok, w256_ok, w257_ok, w258_ok, w259_ok,
    w260_ok, w261_ok, w262_ok, w263_ok, w264_ok, w265_ok, w266_ok, w267_ok,
    w268_ok, w269_ok, w270_ok, w271_ok, w272_ok, w273_ok, w274_ok, w275_ok,
    w276_ok, w277_ok, w278_ok, w279_ok, w280_ok, w281_ok, w282_ok, w283_ok,
    w284_ok, w285_ok, w286_ok, w287_ok, w288_ok, w289_ok, w290_ok, w291_ok,
    w292_ok, w293_ok, w294_ok, w295_ok, w296_ok, w297_ok, w298_ok, w299_ok,
    w300_ok, w301_ok, w302_ok, w303_ok, w304_ok, w305_ok, w306_ok, w307_ok,
    w308_ok, w309_ok, w310_ok, w311_ok, w312_ok, w313_ok, w314_ok, w315_ok,
    w316_ok, w317_ok, w318_ok, w319_ok, w320_ok, w321_ok, w322_ok, w323_ok,
    w324_ok, w325_ok, w326_ok, w327_ok, w328_ok, w329_ok, w330_ok, w331_ok,
    w332_ok, w333_ok, w334_ok, w335_ok, w336_ok, w337_ok, w338_ok, w339_ok,
    w340_ok, w341_ok, w342_ok, w343_ok, w344_ok]

/-- The census, transported to the table-built windows. -/
theorem census_all :
    (buildWindows allRows censusTs).all (fun w => windowExactT w) = true := by
  rw [buildWindows_eq_wlist]
  exact wlist_all

end OneTwoSobolT5.Census

namespace OneTwoSobolT5

/-- Every pair-aligned window's rank profile matches its claimed exact `t`. -/
theorem census_every_window :
    ∀ w ∈ buildWindows allRows censusTs, windowExactT w = true :=
  fun w hw => List.all_eq_true.mp Census.census_all w hw

set_option maxRecDepth 4000 in
/-- Exactly nine windows have `t = 4` and 336 have `t = 5`. -/
theorem census_distribution :
    censusTs.count 4 = 9 ∧ censusTs.count 5 = 336 ∧ censusTs.length = 345 := by
  refine ⟨by decide, by decide, by decide⟩

end OneTwoSobolT5
