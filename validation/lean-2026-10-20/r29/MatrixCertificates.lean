import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators
namespace Erdos670R29

def completion_infinity : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(154907868127150589 / 1923304880250000 : ℝ), (1696688651775479 / 25644065070000 : ℝ), (125479651378551811 / 1923304880250000 : ℝ), (-855013526827973 / 80137703343750 : ℝ), (23678332272023071 / 384660976050000 : ℝ);
    (1696688651775479 / 25644065070000 : ℝ), (60360400398257 / 657540130000 : ℝ), (123342327356291711 / 1282203253500000 : ℝ), (-103654360977957 / 5342513556250 : ℝ), (1382104386128603 / 25644065070000 : ℝ);
    (125479651378551811 / 1923304880250000 : ℝ), (123342327356291711 / 1282203253500000 : ℝ), (65529018175226903 / 641101626750000 : ℝ), (-6486353065612211 / 240413110031250 : ℝ), (18316487478235019 / 384660976050000 : ℝ);
    (-855013526827973 / 80137703343750 : ℝ), (-103654360977957 / 5342513556250 : ℝ), (-6486353065612211 / 240413110031250 : ℝ), (18566550141185716 / 120206555015625 : ℝ), (33932098089378769 / 769321952100000 : ℝ);
    (23678332272023071 / 384660976050000 : ℝ), (1382104386128603 / 25644065070000 : ℝ), (18316487478235019 / 384660976050000 : ℝ), (33932098089378769 / 769321952100000 : ℝ), (2231708054059801 / 15386439042000 : ℝ)]

def completion_infinity_L : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
    (127251648883160925 / 154907868127150589 : ℝ), 1, 0, 0, 0;
    (11407241034413801 / 14082533466104599 : ℝ), (940189106051962783726244985260481 / 826418379305755437956618593630400 : ℝ), 1, 0, 0;
    (-20520324643871352 / 154907868127150589 : ℝ), (-4401708670379836325207292598169 / 15495344611982914461686598630570 : ℝ), (-19823264814784431790740600874691621189601491918560 / 2857769742550140136253930920634931306700264567177 : ℝ), 1, 0;
    (118391661360115355 / 154907868127150589 : ℝ), (734725316100714292495683378729 / 8264183793057554379566185936304 : ℝ), (-19177189492590380806528344572703713557366728500700 / 2857769742550140136253930920634931306700264567177 : ℝ), (1921252513749450223033767133331831316902219064182260320967130125 / 18055884486521964222273206776163857603931042197563329670022013952 : ℝ), 1]

def completion_infinity_D : Fin 5 → ℝ := ![(154907868127150589 / 1923304880250000 : ℝ), (3099068922396582892337319726114 / 82759738543908932041767213125 : ℝ), (2857769742550140136253930920634931306700264567177 / 3178909004094110081469881257834479769519200000000 : ℝ), (4822618719690695572188356510727526069426026227981658565711008 / 45170631923713597997851621407820009950691390253268228678125 : ℝ), (11969803639470114375654033899666963971150011319277788530276681095214814201858963 / 213704435385587440846239719024081948943425507957182994540264378823478087680000 : ℝ)]

theorem completion_infinity_factor :
    completion_infinity_L * Matrix.diagonal completion_infinity_D * completion_infinity_Lᵀ = completion_infinity := by
  ext i j
  change (∑ k : Fin 5, (completion_infinity_L * Matrix.diagonal completion_infinity_D) i k *
    completion_infinity_L j k) = completion_infinity i j
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [completion_infinity, completion_infinity_L, completion_infinity_D, Fin.sum_univ_succ]


theorem completion_infinity_posDef : completion_infinity.PosDef := by
  have htri : completion_infinity_L.IsLowerTriangular := by
    intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> norm_num [completion_infinity_L] at *
  have hdet : completion_infinity_L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    norm_num [completion_infinity_L, Fin.prod_univ_succ]
  have hunit : IsUnit completion_infinity_L := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [hdet]
    exact isUnit_one
  have hdiag : (Matrix.diagonal completion_infinity_D).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [completion_infinity_D]
  have h := hdiag.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, completion_infinity_factor] at h
  exact h

#print axioms completion_infinity_posDef

def completion_k0 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(1394026811024556049 / 17309743922250000 : ℝ), (46328598787702541 / 692389756890000 : ℝ), (381882790308755381 / 5769914640750000 : ℝ), (-9863605491658714 / 1081858995140625 : ℝ), (1092251527626516371 / 17309743922250000 : ℝ);
    (46328598787702541 / 692389756890000 : ℝ), (124223500469139577 / 1331518763250000 : ℝ), (9099428306584243 / 92318634252000 : ℝ), (-68639378160196897 / 4327435980562500 : ℝ), (110547438593911493 / 1923304880250000 : ℝ);
    (381882790308755381 / 5769914640750000 : ℝ), (9099428306584243 / 92318634252000 : ℝ), (1825298239967760569 / 17309743922250000 : ℝ), (-46808311449577981 / 2163717990281250 : ℝ), (306177224272754669 / 5769914640750000 : ℝ);
    (-9863605491658714 / 1081858995140625 : ℝ), (-68639378160196897 / 4327435980562500 : ℝ), (-46808311449577981 / 2163717990281250 : ℝ), (175152359377665304 / 1081858995140625 : ℝ), (1830238021736459117 / 34619487844500000 : ℝ);
    (1092251527626516371 / 17309743922250000 : ℝ), (110547438593911493 / 1923304880250000 : ℝ), (306177224272754669 / 5769914640750000 : ℝ), (1830238021736459117 / 34619487844500000 : ℝ), (894977181933524927 / 5769914640750000 : ℝ)]

def completion_k0_L : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
    (1158214969692563525 / 1394026811024556049 : ℝ), 1, 0, 0, 0;
    (1145648370926266143 / 1394026811024556049 : ℝ), (701001149239642661585311528660832325 / 606506437835320855794175275045360616 : ℝ), 1, 0, 0;
    (-157817687866539424 / 1394026811024556049 : ℝ), (-49988431305044237060027259593152553 / 227439914188245320922815728142010231 : ℝ), (-95808687642163620578013701553598383430821956996062360 / 14511543996807096861690871210606487595401269863065701 : ℝ), 1, 0;
    (1092251527626516371 / 1394026811024556049 : ℝ), (60946384821714233961183041071986319 / 454879828376490641845631456284020462 : ℝ), (-97249975348567947158845090161863269255545192027701580 / 14511543996807096861690871210606487595401269863065701 : ℝ), (3540868483579262142574972748292894248293979898053213181968089309757551 / 14946270143939288956934877871713144894543430749669055765832500920369152 : ℝ), 1]

def completion_k0_D : Fin 5 → ℝ := ![(1394026811024556049 / 17309743922250000 : ℝ), (75813304729415106974271909380670077 / 2010853926632154863723518599187500 : ℝ), (14511543996807096861690871210606487595401269863065701 / 20996942252250885259923788328335306031731032212000000 : ℝ), (35928533999854059992631917960848905996498631609781384052481973366272 / 278688362242450205222619016415794913155603344743491428591552234375 : ℝ), (295064111565677587494222415859176640559512433739282003640599757740230038816292365092873 / 4422497586057431447782735798785173077500115685602524773359238496032093334331392000000 : ℝ)]

theorem completion_k0_factor :
    completion_k0_L * Matrix.diagonal completion_k0_D * completion_k0_Lᵀ = completion_k0 := by
  ext i j
  change (∑ k : Fin 5, (completion_k0_L * Matrix.diagonal completion_k0_D) i k *
    completion_k0_L j k) = completion_k0 i j
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [completion_k0, completion_k0_L, completion_k0_D, Fin.sum_univ_succ]


theorem completion_k0_posDef : completion_k0.PosDef := by
  have htri : completion_k0_L.IsLowerTriangular := by
    intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> norm_num [completion_k0_L] at *
  have hdet : completion_k0_L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    norm_num [completion_k0_L, Fin.prod_univ_succ]
  have hunit : IsUnit completion_k0_L := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [hdet]
    exact isUnit_one
  have hdiag : (Matrix.diagonal completion_k0_D).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [completion_k0_D]
  have h := hdiag.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, completion_k0_factor] at h
  exact h

#print axioms completion_k0_posDef

def macroGram : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(40846909 / 250000 : ℝ), (1576997 / 10000 : ℝ), (41367491 / 250000 : ℝ), (3749361 / 31250 : ℝ), (9827551 / 50000 : ℝ);
    (1576997 / 10000 : ℝ), (2673189 / 10000 : ℝ), (144778173 / 500000 : ℝ), (1528947 / 6250 : ℝ), (3186129 / 10000 : ℝ);
    (41367491 / 250000 : ℝ), (144778173 / 500000 : ℝ), (95402629 / 250000 : ℝ), (11540109 / 31250 : ℝ), (22033739 / 50000 : ℝ);
    (3749361 / 31250 : ℝ), (1528947 / 6250 : ℝ), (11540109 / 31250 : ℝ), (13487796 / 15625 : ℝ), (74121489 / 100000 : ℝ);
    (9827551 / 50000 : ℝ), (3186129 / 10000 : ℝ), (22033739 / 50000 : ℝ), (74121489 / 100000 : ℝ), (1884761 / 2000 : ℝ)]

def macroGram_L : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
    (39424925 / 40846909 : ℝ), 1, 0, 0, 0;
    (41367491 / 40846909 : ℝ), (2651920397490907 / 2350925968628800 : ℝ), 1, 0, 0;
    (29994888 / 40846909 : ℝ), (16444551865119 / 14693287303930 : ℝ), (17204047980065279905440 / 11344946112641979397877 : ℝ), 1, 0;
    (49137755 / 40846909 : ℝ), (26326714551763 / 23509259686288 : ℝ), (113091931577409573265100 / 79414622788493855785139 : ℝ), (115989202024860860556311618375 / 179843218143509606247601277952 : ℝ), 1]

def macroGram_D : Fin 5 → ℝ := ![(40846909 / 250000 : ℝ), (2938657460786 / 25529318125 : ℝ), (79414622788493855785139 / 1175462984314400000000 : ℝ), (16860301700954025585712619808 / 35452956602006185618365625 : ℝ), (271870469926137074239387919119179863 / 1198954787623397374984008519680000 : ℝ)]

theorem macroGram_factor :
    macroGram_L * Matrix.diagonal macroGram_D * macroGram_Lᵀ = macroGram := by
  ext i j
  change (∑ k : Fin 5, (macroGram_L * Matrix.diagonal macroGram_D) i k *
    macroGram_L j k) = macroGram i j
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [macroGram, macroGram_L, macroGram_D, Fin.sum_univ_succ]


theorem macroGram_posDef : macroGram.PosDef := by
  have htri : macroGram_L.IsLowerTriangular := by
    intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> norm_num [macroGram_L] at *
  have hdet : macroGram_L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    norm_num [macroGram_L, Fin.prod_univ_succ]
  have hunit : IsUnit macroGram_L := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [hdet]
    exact isUnit_one
  have hdiag : (Matrix.diagonal macroGram_D).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [macroGram_D]
  have h := hdiag.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, macroGram_factor] at h
  exact h

#print axioms macroGram_posDef

end Erdos670R29
