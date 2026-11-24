import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Set.Defs

namespace PEqualNP.Outside.L_meta_1620_aux

abbrev V := (Fin 14 → Bool) → Bool
abbrev Signature := ℕ × ℕ

def enc : List ℕ → V → ℕ
  | [], _ => 0
  | x::xs, f => Nat.bit (f (fun i => x.testBit i.val)) (enc xs f)

lemma enc_and (xs : List ℕ) (f g : V) :
    enc xs (fun z => f z && g z) = enc xs f &&& enc xs g := by
  induction xs with
  | nil => simp [enc]
  | cons x xs ih => simp only [enc, Nat.land_bit, ih]

lemma enc_or (xs : List ℕ) (f g : V) :
    enc xs (fun z => f z || g z) = enc xs f ||| enc xs g := by
  induction xs with
  | nil => simp [enc]
  | cons x xs ih => simp only [enc, Nat.lor_bit, ih]

def both (a b : Signature) : Signature := (a.1 &&& b.1, a.2 &&& b.2)
def either (a b : Signature) : Signature := (a.1 ||| b.1, a.2 ||| b.2)

def pc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, a => pc k a + (a.testBit k).toNat

lemma band (k a b : ℕ) : pc k (a &&& b) ≤ pc k a ∧ pc k (a &&& b) ≤ pc k b ∧
    pc k a + pc k b ≤ pc k (a &&& b) + k := by
  induction k with
  | zero => simp [pc]
  | succ k ih =>
    simp only [pc,Nat.testBit_and]
    cases a.testBit k <;> cases b.testBit k <;> simp_all <;> omega

lemma bor (k a b : ℕ) : pc k a ≤ pc k (a ||| b) ∧ pc k b ≤ pc k (a ||| b) ∧
    pc k (a ||| b) ≤ pc k a + pc k b := by
  induction k with
  | zero => simp [pc]
  | succ k ih =>
    simp only [pc,Nat.testBit_or]
    cases a.testBit k <;> cases b.testBit k <;> simp_all <;> omega

abbrev E (s : Signature) := pc 21 s.1
abbrev Z (s : Signature) := pc 37 s.2

def byte (a : ℕ) : ℕ :=
  (95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224 >>> (4*(a%256))) % 16

lemma pc_add (k n a : ℕ) : pc (k+n) a = pc k a + pc n (a >>> k) := by
  induction n with
  | zero => simp [pc]
  | succ n ih =>
    change pc (k+n) a + (a.testBit (k+n)).toNat =
      pc k a + (pc n (a >>> k) + ((a >>> k).testBit n).toNat)
    rw [ih,Nat.testBit_shiftRight,Nat.add_assoc]

lemma pc_mod (a n k : ℕ) (h : k ≤ n) : pc k (a % 2^n) = pc k a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have lt : k < n := by omega
    simp [pc,Nat.testBit_mod_two_pow,lt,ih (by omega)]

lemma byte_correct (a : ℕ) : byte a = pc 8 a := by
  have table : ∀ i : Fin 256, byte i.val = pc 8 i.val := by decide +kernel
  have t := table ⟨a%256,Nat.mod_lt _ (by decide)⟩
  have e : pc 8 (a%256) = pc 8 a := pc_mod a 8 8 (by rfl)
  simpa only [byte,Nat.mod_mod,e] using t

def ec (s : Signature) := pc 5 s.1 + byte (s.1 >>> 5) + byte (s.1 >>> 13)
def zc (s : Signature) := pc 5 s.2 + byte (s.2 >>> 5) + byte (s.2 >>> 13) +
  byte (s.2 >>> 21) + byte (s.2 >>> 29)

lemma ec_correct (s : Signature) : ec s = E s := by
  have h1 := pc_add 5 8 s.1
  have h2 := pc_add 13 8 s.1
  change pc 13 s.1 = _ at h1
  change pc 21 s.1 = _ at h2
  simp only [ec,byte_correct,E]
  rw [h2,h1]

lemma zc_correct (s : Signature) : zc s = Z s := by
  have h1 := pc_add 5 8 s.2
  have h2 := pc_add 13 8 s.2
  have h3 := pc_add 21 8 s.2
  have h4 := pc_add 29 8 s.2
  change pc 13 s.2 = _ at h1
  change pc 21 s.2 = _ at h2
  change pc 29 s.2 = _ at h3
  change pc 37 s.2 = _ at h4
  simp only [zc,byte_correct,Z]
  rw [h4,h3,h2,h1]

def Reach (atoms : List Signature) : ℕ → Signature → Prop
  | 0, s => s ∈ atoms
  | k+1, s => ∃ a b, Reach atoms k a ∧ Reach atoms k b ∧ (s = both a b ∨ s = either a b)

lemma promote {atoms : List Signature} {k : ℕ} {s : Signature} (h : Reach atoms k s) :
    Reach atoms (k+1) s := by
  exact ⟨s,s,h,h,Or.inl (by simp [both])⟩

def pos : List ℕ := [129,
  130,
  136,
  257,
  260,
  320,
  514,
  544,
  576,
  1025,
  1040,
  1056,
  2056,
  2064,
  2112,
  4100,
  4104,
  4128,
  8194,
  8196,
  8208]

def neg : List ℕ := [127,
  244,
  314,
  432,
  541,
  660,
  792,
  1102,
  1220,
  1290,
  1548,
  2087,
  2212,
  2338,
  2565,
  3078,
  3716,
  4179,
  4304,
  4370,
  4625,
  5008,
  5186,
  6147,
  7426,
  8297,
  8416,
  8488,
  8713,
  9288,
  9992,
  10273,
  10656,
  12353,
  13504,
  14849,
  16256]

def atoms : List Signature := [(521,45408733201),
  (262210,30059141),
  (557072,122291),
  (69636,2046822101),
  (1057792,4063359),
  (133248,6677346319),
  (16672,26411925891),
  (7,90263851306),
  (56,74241811020),
  (448,104424621168),
  (3584,87531030400),
  (28672,109546960896),
  (229376,128882442240),
  (1835008,137405399040)]

def ones : List Signature := [(0,15),
  (0,51),
  (0,85),
  (0,387),
  (0,645),
  (0,1169),
  (0,6147),
  (0,10245),
  (0,18449),
  (0,34945),
  (0,69922),
  (0,82992),
  (0,99712),
  (0,120832),
  (0,393219),
  (0,655365),
  (0,1179665),
  (0,2359338),
  (0,2621516),
  (0,3145840),
  (0,4063232),
  (0,4325505),
  (0,8521729),
  (0,17310212),
  (0,21004928),
  (0,25208832),
  (0,30015488),
  (0,100663299),
  (0,167772165),
  (0,301989905),
  (0,570425473),
  (0,1207960132),
  (0,1342178384),
  (0,1610614400),
  (0,2046820352),
  (0,2181040129),
  (0,4362080266),
  (0,4429193228),
  (0,6442465280),
  (0,6677331968),
  (0,8623620097),
  (0,17247240450),
  (0,17720934784),
  (0,25774391296),
  (0,26407337984),
  (0,34629238800),
  (0,36515629056),
  (0,42959241216),
  (0,45399146496),
  (0,68721639456),
  (0,68736352256),
  (0,68738875392),
  (0,69793285120),
  (0,69795315776),
  (0,69809996288),
  (0,73014513664),
  (0,73016541192),
  (0,73031229440),
  (0,74222403584),
  (0,85899411712),
  (0,85901705216),
  (0,85920317440),
  (0,87509958656),
  (0,90261422080),
  (0,103079297024),
  (0,103082360832),
  (0,103104380928),
  (0,104421392384),
  (0,109521666048),
  (0,128849018880),
  (1,0),
  (2,0),
  (4,0),
  (7,90263851306),
  (8,0),
  (16,0),
  (32,0),
  (56,74241811020),
  (63,91489121134),
  (64,0),
  (128,0),
  (256,0),
  (448,104424621168),
  (455,125966833018),
  (504,108871116412),
  (512,0),
  (521,45408733201),
  (527,135672584507),
  (569,119650544221),
  (969,115204115569),
  (1024,0),
  (2048,0),
  (3584,87531030400),
  (3591,91895469994),
  (3593,132939763601),
  (3640,91962845132),
  (4032,122162366448),
  (4096,0),
  (8192,0),
  (16384,0),
  (16672,26411925891),
  (16679,99428536747),
  (16696,100653736911),
  (16864,130836547059),
  (17193,63197038995),
  (20256,96222021507),
  (28672,109546960896),
  (28679,126796298538),
  (28728,110757542476),
  (28960,135958886787),
  (29120,110892285040),
  (29193,118440065041),
  (32256,128341639040),
  (32768,0),
  (65536,0),
  (69636,2046822101),
  (69639,92310673407),
  (69692,75080672989),
  (70084,105129264885),
  (70157,47153565397),
  (73220,87967238101),
  (86308,27888322519),
  (94212,111593782997),
  (131072,0),
  (133248,6677346319),
  (133255,92579117359),
  (133304,76489964111),
  (133568,111101967487),
  (133769,49905039391),
  (134784,94208376719),
  (149920,32988608911),
  (161920,109781841935),
  (202884,8556396255),
  (229376,128882442240),
  (229383,133244588330),
  (229432,134385377868),
  (229824,130224702576),
  (229897,131331934225),
  (231552,135559788559),
  (232960,130493155200),
  (233476,130929264341),
  (246048,129519976835),
  (258048,135325022208),
  (262144,0),
  (262210,30059141),
  (262215,90293910447),
  (262266,74254559949),
  (262594,104454680309),
  (262731,45430270613),
  (265794,87540084613),
  (278882,26437659527),
  (290882,109551811205),
  (331846,2076880597),
  (395458,6707395215),
  (491586,128882485893),
  (524288,0),
  (557072,122291),
  (557079,90263903675),
  (557112,74241933311),
  (557520,104424660467),
  (557593,45408837043),
  (560656,87531052979),
  (573744,26412047795),
  (585744,109546962355),
  (626708,2046943223),
  (690320,6677462463),
  (753680,128882564531),
  (819282,30146487),
  (1048576,0),
  (1057792,4063359),
  (1057799,90265555327),
  (1057848,74243252863),
  (1058240,104425538687),
  (1058313,45411616895),
  (1060352,87535093759),
  (1074464,26415596031),
  (1078272,109551024255),
  (1127428,2050885375),
  (1191040,6681409663),
  (1287168,128882442367),
  (1320002,33467135),
  (1614864,4185599),
  (1835008,137405399040),
  (1835015,137407828266),
  (1835064,137424806476),
  (1835074,137435458181),
  (1835456,137408627824),
  (1835529,137414985745),
  (1838592,137426470784),
  (1844224,137409462399),
  (1851680,137409986947),
  (1863680,137430693888),
  (1867792,137405521331),
  (1904644,137405400789),
  (1968256,137405413391),
  (2064384,137438822400)]

def excAnd : List Signature := [(73724,126625638397),
  (161983,128038337391),
  (249639,134888789931),
  (259017,136700755057),
  (294522,128478609357),
  (335486,92273356765),
  (352102,96633597911),
  (424186,110862531279),
  (424651,118646110879),
  (465150,77308018399),
  (495226,134922350541),
  (508779,131935955863),
  (511842,130593828743),
  (520314,136532982477),
  (520779,135627012757),
  (523842,136935636869),
  (561111,126524710907),
  (577335,100519108539),
  (586199,128139525627),
  (586713,119515905523),
  (589335,128411107259),
  (589776,128613220339),
  (627677,115875241975),
  (630740,122330144759),
  (646964,96624697335),
  (706999,101710298559),
  (718999,126964071871),
  (719513,118641393087),
  (839538,96230965175),
  (848475,118444785591),
  (851538,128342294455),
  (892502,87976312823),
  (981202,109786693567),
  (1058303,126118492031),
  (1127932,109441935103),
  (1128397,115875991295),
  (1191103,93671340927),
  (1207719,101711821311),
  (1260732,77296713471),
  (1287231,134452556671),
  (1287623,134586783103),
  (1287672,134653896319),
  (1288137,132405742719),
  (1303847,133815013887),
  (1304361,131935914495),
  (1389694,75094732543),
  (1453306,76504021759),
  (1549434,134385412863),
  (1549899,131331975935),
  (1566050,129520020479),
  (1615319,125967523327),
  (1615833,115204939263),
  (1631543,99430161919),
  (1684948,105130221567),
  (1748119,92580871679),
  (1855271,137428965291),
  (1864649,137433971825),
  (1905148,137425938173),
  (1905613,137417150197),
  (1908284,137429100509),
  (1908676,137429633013),
  (1921837,137419444183),
  (1924900,137426864087),
  (1968319,137425140591),
  (1984935,137412164015),
  (1985449,137419454879),
  (1996935,137433053487),
  (1996984,137433315919),
  (1997449,137431873567),
  (2037948,137424813791),
  (2038413,137414999775),
  (2054564,137410002911),
  (2065353,137438907505),
  (2081063,137438892459),
  (2081577,137438841235),
  (2084640,137438922627),
  (2093577,137438951441)]

def excOr : List Signature := [(511,126118360958),
  (3647,92030220270),
  (4039,126524708858),
  (4088,126592083964),
  (20263,100519090091),
  (28735,128004782958),
  (29127,128139525498),
  (29176,111027027580),
  (29641,119515905137),
  (32263,128411107242),
  (32312,128478478284),
  (32704,128613220336),
  (70140,109441541885),
  (70605,115875204853),
  (73276,92264835037),
  (73668,122330138613),
  (86829,64405000151),
  (89892,96624674775),
  (133311,93670161263),
  (149927,101710248367),
  (150441,67626236319),
  (161927,126964070703),
  (161976,110858205775),
  (162441,118641391647),
  (202940,77295271647),
  (203405,51515653855),
  (219556,34330787807),
  (229439,134452556654),
  (229831,134586783098),
  (229880,134653896316),
  (230345,132405742705),
  (232967,134855235498),
  (233016,134922348492),
  (233408,130761607152),
  (246055,133815013803),
  (246569,131935914387),
  (249632,130593818499),
  (258055,135392131370),
  (258104,136532982348),
  (258496,136667200624),
  (258569,135627012113),
  (261632,136935636864),
  (265850,91971366861),
  (279403,63214381975),
  (282466,96230944647),
  (290938,110761867981),
  (291403,118444784277),
  (294466,128342294405),
  (331902,75093421789),
  (332367,47175102165),
  (335430,87976292309),
  (335486,92273356765),
  (348518,27914055639),
  (395514,76502710991),
  (395979,49926568607),
  (412130,33014332303),
  (424130,109786692239),
  (424186,110862531279),
  (465094,8586444511),
  (491642,134385412813),
  (492107,131331975829),
  (495170,130493165445),
  (508258,129520020359),
  (511842,130593828743),
  (520258,135325022853),
  (520779,135627012757),
  (557527,125966867963),
  (558041,115204152819),
  (560663,91895488443),
  (561104,122162372595),
  (573751,99428588987),
  (574265,63197142451),
  (577328,96222044083),
  (577335,100519108539),
  (585751,126796299707),
  (586192,110892285427),
  (586265,118440066483),
  (586713,119515905523),
  (589328,128341639091),
  (627156,105129304055),
  (627229,47153668087),
  (630292,87967260663),
  (630740,122330144759),
  (643380,27888443383),
  (690327,92579167679),
  (690841,49905139135),
  (706992,32988724671),
  (718992,109781843391),
  (718999,126964071871),
  (759956,8556511231),
  (819803,45430341559),
  (822866,87540105143),
  (835954,26437746615),
  (847954,109551812535),
  (851538,128342294455),
  (888918,2076966903),
  (952530,6707478463),
  (1057855,91490300799),
  (1058247,125967488383),
  (1058296,108871509631),
  (1058761,115204902015),
  (1074471,99430109695),
  (1074985,63199660543),
  (1127484,75082114815),
  (1127876,105130182399),
  (1127932,109441935103),
  (1127949,47156449023),
  (1144100,27891992575),
  (1191047,92580821375),
  (1191096,76491405951),
  (1191103,93671340927),
  (1191561,49907923071),
  (1207712,32992279039),
  (1260676,8560459519),
  (1287175,133244588415),
  (1287224,134385377919),
  (1287616,130224702591),
  (1287689,131331934335),
  (1288137,132405742719),
  (1303840,129519976959),
  (1303847,133815013887),
  (1320058,74255870719),
  (1320523,45432630015),
  (1336674,26440805375),
  (1389638,2080288511),
  (1453250,6710803199),
  (1549378,128882486015),
  (1549434,134385412863),
  (1614871,90265607679),
  (1615312,104425577983),
  (1615319,125967523327),
  (1615385,45411720703),
  (1631536,26415717887),
  (1684500,2051006463),
  (1748112,6681525759),
  (1835071,137425138542),
  (1835463,137408894330),
  (1835512,137425938044),
  (1835977,137417149553),
  (1838599,137428834218),
  (1838648,137429100492),
  (1839040,137429633008),
  (1851687,137412153771),
  (1852201,137419442579),
  (1855264,137426864003),
  (1863687,137433053482),
  (1863736,137433315916),
  (1864128,137433840752),
  (1864201,137431873553),
  (1867264,137434890112),
  (1877074,33554431),
  (1904700,137424807645),
  (1905092,137408628469),
  (1905165,137414987477),
  (1905613,137417150197),
  (1908228,137426470869),
  (1921316,137409988567),
  (1924900,137426864087),
  (1968263,137407838511),
  (1968312,137424812623),
  (1968777,137414998047),
  (1984928,137410001295),
  (1984935,137412164015),
  (1996928,137430693903),
  (1997449,137431873567),
  (2037892,137405415135),
  (2037948,137424813791),
  (2064391,137438892330),
  (2064440,137438831180),
  (2064832,137438905456),
  (2064905,137438840849),
  (2067968,137438922624),
  (2081056,137438822787),
  (2081577,137438841235),
  (2093056,137438951424)]


def sig (f : V) : Signature := (enc pos f,enc neg f)

def twoOK (s : Signature) : Prop :=
  E s ≤ 12 ∧ (Z s = 0 → E s ≤ 2) ∧ (5 ≤ E s → 19 ≤ Z s) ∧
  (11 ≤ E s → 27 ≤ Z s) ∧
  (11 ≤ E s → Z s ≤ 28 → s ∈ excAnd) ∧ (9 ≤ E s → Z s ≤ 27 → s ∈ excOr)

def testTwo (s : Signature) : Bool :=
  let p := ec s
  let n := zc s
  decide (p ≤ 12) && (decide (n ≠ 0) || decide (p ≤ 2)) &&
    (decide (p < 5) || decide (19 ≤ n)) && (decide (p < 11) || decide (27 ≤ n)) &&
    (decide (p < 11) || decide (28 < n) || excAnd.contains s) &&
    (decide (p < 9) || decide (27 < n) || excOr.contains s)

lemma test_sound (s : Signature) (h : testTwo s = true) : twoOK s := by
  simp only [testTwo,ec_correct,zc_correct,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,List.contains_iff_mem] at h
  unfold twoOK
  grind

lemma one_closed : atoms.all (fun a => atoms.all (fun b =>
    ones.contains (both a b) && ones.contains (either a b))) = true := by decide +kernel

lemma one_mem {s} (h : Reach atoms 1 s) : s ∈ ones := by
  obtain ⟨a,b,ha,hb,hm|hm⟩ := h <;> subst s
  · exact List.contains_iff_mem.mp ((Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp (List.all_eq_true.mp one_closed a ha) b hb)).1)
  · exact List.contains_iff_mem.mp ((Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp (List.all_eq_true.mp one_closed a ha) b hb)).2)

def chunk0 : List Signature := [(0,15),
  (0,51),
  (0,85),
  (0,387),
  (0,645),
  (0,1169),
  (0,6147),
  (0,10245)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert0 : (chunk0).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk1 : List Signature := [(0,18449),
  (0,34945),
  (0,69922),
  (0,82992),
  (0,99712),
  (0,120832),
  (0,393219),
  (0,655365)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert1 : (chunk1).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk2 : List Signature := [(0,1179665),
  (0,2359338),
  (0,2621516),
  (0,3145840),
  (0,4063232),
  (0,4325505),
  (0,8521729),
  (0,17310212)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert2 : (chunk2).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk3 : List Signature := [(0,21004928),
  (0,25208832),
  (0,30015488),
  (0,100663299),
  (0,167772165),
  (0,301989905),
  (0,570425473),
  (0,1207960132)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert3 : (chunk3).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk4 : List Signature := [(0,1342178384),
  (0,1610614400),
  (0,2046820352),
  (0,2181040129),
  (0,4362080266),
  (0,4429193228),
  (0,6442465280),
  (0,6677331968)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert4 : (chunk4).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk5 : List Signature := [(0,8623620097),
  (0,17247240450),
  (0,17720934784),
  (0,25774391296),
  (0,26407337984),
  (0,34629238800),
  (0,36515629056),
  (0,42959241216)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert5 : (chunk5).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk6 : List Signature := [(0,45399146496),
  (0,68721639456),
  (0,68736352256),
  (0,68738875392),
  (0,69793285120),
  (0,69795315776),
  (0,69809996288),
  (0,73014513664)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert6 : (chunk6).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk7 : List Signature := [(0,73016541192),
  (0,73031229440),
  (0,74222403584),
  (0,85899411712),
  (0,85901705216),
  (0,85920317440),
  (0,87509958656),
  (0,90261422080)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert7 : (chunk7).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk8 : List Signature := [(0,103079297024),
  (0,103082360832),
  (0,103104380928),
  (0,104421392384),
  (0,109521666048),
  (0,128849018880),
  (1,0),
  (2,0)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert8 : (chunk8).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk9 : List Signature := [(4,0),
  (7,90263851306),
  (8,0),
  (16,0),
  (32,0),
  (56,74241811020),
  (63,91489121134),
  (64,0)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert9 : (chunk9).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk10 : List Signature := [(128,0),
  (256,0),
  (448,104424621168),
  (455,125966833018),
  (504,108871116412),
  (512,0),
  (521,45408733201),
  (527,135672584507)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert10 : (chunk10).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk11 : List Signature := [(569,119650544221),
  (969,115204115569),
  (1024,0),
  (2048,0),
  (3584,87531030400),
  (3591,91895469994),
  (3593,132939763601),
  (3640,91962845132)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert11 : (chunk11).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk12 : List Signature := [(4032,122162366448),
  (4096,0),
  (8192,0),
  (16384,0),
  (16672,26411925891),
  (16679,99428536747),
  (16696,100653736911),
  (16864,130836547059)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert12 : (chunk12).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk13 : List Signature := [(17193,63197038995),
  (20256,96222021507),
  (28672,109546960896),
  (28679,126796298538),
  (28728,110757542476),
  (28960,135958886787),
  (29120,110892285040),
  (29193,118440065041)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert13 : (chunk13).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk14 : List Signature := [(32256,128341639040),
  (32768,0),
  (65536,0),
  (69636,2046822101),
  (69639,92310673407),
  (69692,75080672989),
  (70084,105129264885),
  (70157,47153565397)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert14 : (chunk14).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk15 : List Signature := [(73220,87967238101),
  (86308,27888322519),
  (94212,111593782997),
  (131072,0),
  (133248,6677346319),
  (133255,92579117359),
  (133304,76489964111),
  (133568,111101967487)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert15 : (chunk15).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk16 : List Signature := [(133769,49905039391),
  (134784,94208376719),
  (149920,32988608911),
  (161920,109781841935),
  (202884,8556396255),
  (229376,128882442240),
  (229383,133244588330),
  (229432,134385377868)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert16 : (chunk16).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk17 : List Signature := [(229824,130224702576),
  (229897,131331934225),
  (231552,135559788559),
  (232960,130493155200),
  (233476,130929264341),
  (246048,129519976835),
  (258048,135325022208),
  (262144,0)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert17 : (chunk17).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk18 : List Signature := [(262210,30059141),
  (262215,90293910447),
  (262266,74254559949),
  (262594,104454680309),
  (262731,45430270613),
  (265794,87540084613),
  (278882,26437659527),
  (290882,109551811205)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert18 : (chunk18).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk19 : List Signature := [(331846,2076880597),
  (395458,6707395215),
  (491586,128882485893),
  (524288,0),
  (557072,122291),
  (557079,90263903675),
  (557112,74241933311),
  (557520,104424660467)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert19 : (chunk19).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk20 : List Signature := [(557593,45408837043),
  (560656,87531052979),
  (573744,26412047795),
  (585744,109546962355),
  (626708,2046943223),
  (690320,6677462463),
  (753680,128882564531),
  (819282,30146487)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert20 : (chunk20).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk21 : List Signature := [(1048576,0),
  (1057792,4063359),
  (1057799,90265555327),
  (1057848,74243252863),
  (1058240,104425538687),
  (1058313,45411616895),
  (1060352,87535093759),
  (1074464,26415596031)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert21 : (chunk21).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk22 : List Signature := [(1078272,109551024255),
  (1127428,2050885375),
  (1191040,6681409663),
  (1287168,128882442367),
  (1320002,33467135),
  (1614864,4185599),
  (1835008,137405399040),
  (1835015,137407828266)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert22 : (chunk22).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk23 : List Signature := [(1835064,137424806476),
  (1835074,137435458181),
  (1835456,137408627824),
  (1835529,137414985745),
  (1838592,137426470784),
  (1844224,137409462399),
  (1851680,137409986947),
  (1863680,137430693888)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert23 : (chunk23).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

def chunk24 : List Signature := [(1867792,137405521331),
  (1904644,137405400789),
  (1968256,137405413391),
  (2064384,137438822400)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma chunkcert24 : (chunk24).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by decide +kernel

lemma chunkcert : (chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++ chunk9 ++ chunk10 ++ chunk11 ++ chunk12 ++ chunk13 ++ chunk14 ++ chunk15 ++ chunk16 ++ chunk17 ++ chunk18 ++ chunk19 ++ chunk20 ++ chunk21 ++ chunk22 ++ chunk23 ++ chunk24).all (fun a => ones.all (fun b => testTwo (both a b) && testTwo (either a b))) = true := by
  simp only [List.all_append,chunkcert0,chunkcert1,chunkcert2,chunkcert3,chunkcert4,chunkcert5,chunkcert6,chunkcert7,chunkcert8,chunkcert9,chunkcert10,chunkcert11,chunkcert12,chunkcert13,chunkcert14,chunkcert15,chunkcert16,chunkcert17,chunkcert18,chunkcert19,chunkcert20,chunkcert21,chunkcert22,chunkcert23,chunkcert24,Bool.and_self]

def hardAnd0 : List Signature := [(73724,126625638397),
  (161983,128038337391),
  (249639,134888789931),
  (259017,136700755057),
  (294522,128478609357),
  (335486,92273356765),
  (352102,96633597911),
  (424186,110862531279)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardAndcert0 : (hardAnd0).all (fun a => excAnd.all (fun b => decide (19 ≤ zc (both a b)))) = true := by decide +kernel

def hardAnd1 : List Signature := [(424651,118646110879),
  (465150,77308018399),
  (495226,134922350541),
  (508779,131935955863),
  (511842,130593828743),
  (520314,136532982477),
  (520779,135627012757),
  (523842,136935636869)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardAndcert1 : (hardAnd1).all (fun a => excAnd.all (fun b => decide (19 ≤ zc (both a b)))) = true := by decide +kernel

def hardAnd2 : List Signature := [(561111,126524710907),
  (577335,100519108539),
  (586199,128139525627),
  (586713,119515905523),
  (589335,128411107259),
  (589776,128613220339),
  (627677,115875241975),
  (630740,122330144759)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardAndcert2 : (hardAnd2).all (fun a => excAnd.all (fun b => decide (19 ≤ zc (both a b)))) = true := by decide +kernel

def hardAnd3 : List Signature := [(646964,96624697335),
  (706999,101710298559),
  (718999,126964071871),
  (719513,118641393087),
  (839538,96230965175),
  (848475,118444785591),
  (851538,128342294455),
  (892502,87976312823)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardAndcert3 : (hardAnd3).all (fun a => excAnd.all (fun b => decide (19 ≤ zc (both a b)))) = true := by decide +kernel

def hardAnd4 : List Signature := [(981202,109786693567),
  (1058303,126118492031),
  (1127932,109441935103),
  (1128397,115875991295),
  (1191103,93671340927),
  (1207719,101711821311),
  (1260732,77296713471),
  (1287231,134452556671)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardAndcert4 : (hardAnd4).all (fun a => excAnd.all (fun b => decide (19 ≤ zc (both a b)))) = true := by decide +kernel

def hardAnd5 : List Signature := [(1287623,134586783103),
  (1287672,134653896319),
  (1288137,132405742719),
  (1303847,133815013887),
  (1304361,131935914495),
  (1389694,75094732543),
  (1453306,76504021759),
  (1549434,134385412863)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardAndcert5 : (hardAnd5).all (fun a => excAnd.all (fun b => decide (19 ≤ zc (both a b)))) = true := by decide +kernel

def hardAnd6 : List Signature := [(1549899,131331975935),
  (1566050,129520020479),
  (1615319,125967523327),
  (1615833,115204939263),
  (1631543,99430161919),
  (1684948,105130221567),
  (1748119,92580871679),
  (1855271,137428965291)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardAndcert6 : (hardAnd6).all (fun a => excAnd.all (fun b => decide (19 ≤ zc (both a b)))) = true := by decide +kernel

def hardAnd7 : List Signature := [(1864649,137433971825),
  (1905148,137425938173),
  (1905613,137417150197),
  (1908284,137429100509),
  (1908676,137429633013),
  (1921837,137419444183),
  (1924900,137426864087),
  (1968319,137425140591)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardAndcert7 : (hardAnd7).all (fun a => excAnd.all (fun b => decide (19 ≤ zc (both a b)))) = true := by decide +kernel

def hardAnd8 : List Signature := [(1984935,137412164015),
  (1985449,137419454879),
  (1996935,137433053487),
  (1996984,137433315919),
  (1997449,137431873567),
  (2037948,137424813791),
  (2038413,137414999775),
  (2054564,137410002911)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardAndcert8 : (hardAnd8).all (fun a => excAnd.all (fun b => decide (19 ≤ zc (both a b)))) = true := by decide +kernel

def hardAnd9 : List Signature := [(2065353,137438907505),
  (2081063,137438892459),
  (2081577,137438841235),
  (2084640,137438922627),
  (2093577,137438951441)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardAndcert9 : (hardAnd9).all (fun a => excAnd.all (fun b => decide (19 ≤ zc (both a b)))) = true := by decide +kernel

lemma hardAndcert : (hardAnd0 ++ hardAnd1 ++ hardAnd2 ++ hardAnd3 ++ hardAnd4 ++ hardAnd5 ++ hardAnd6 ++ hardAnd7 ++ hardAnd8 ++ hardAnd9).all (fun a => excAnd.all (fun b => decide (19 ≤ zc (both a b)))) = true := by
  simp only [List.all_append,hardAndcert0,hardAndcert1,hardAndcert2,hardAndcert3,hardAndcert4,hardAndcert5,hardAndcert6,hardAndcert7,hardAndcert8,hardAndcert9,Bool.and_self]

def hardOr0 : List Signature := [(511,126118360958),
  (3647,92030220270),
  (4039,126524708858),
  (4088,126592083964),
  (20263,100519090091),
  (28735,128004782958),
  (29127,128139525498),
  (29176,111027027580)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert0 : (hardOr0).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr1 : List Signature := [(29641,119515905137),
  (32263,128411107242),
  (32312,128478478284),
  (32704,128613220336),
  (70140,109441541885),
  (70605,115875204853),
  (73276,92264835037),
  (73668,122330138613)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert1 : (hardOr1).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr2 : List Signature := [(86829,64405000151),
  (89892,96624674775),
  (133311,93670161263),
  (149927,101710248367),
  (150441,67626236319),
  (161927,126964070703),
  (161976,110858205775),
  (162441,118641391647)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert2 : (hardOr2).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr3 : List Signature := [(202940,77295271647),
  (203405,51515653855),
  (219556,34330787807),
  (229439,134452556654),
  (229831,134586783098),
  (229880,134653896316),
  (230345,132405742705),
  (232967,134855235498)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert3 : (hardOr3).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr4 : List Signature := [(233016,134922348492),
  (233408,130761607152),
  (246055,133815013803),
  (246569,131935914387),
  (249632,130593818499),
  (258055,135392131370),
  (258104,136532982348),
  (258496,136667200624)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert4 : (hardOr4).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr5 : List Signature := [(258569,135627012113),
  (261632,136935636864),
  (265850,91971366861),
  (279403,63214381975),
  (282466,96230944647),
  (290938,110761867981),
  (291403,118444784277),
  (294466,128342294405)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert5 : (hardOr5).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr6 : List Signature := [(331902,75093421789),
  (332367,47175102165),
  (335430,87976292309),
  (335486,92273356765),
  (348518,27914055639),
  (395514,76502710991),
  (395979,49926568607),
  (412130,33014332303)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert6 : (hardOr6).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr7 : List Signature := [(424130,109786692239),
  (424186,110862531279),
  (465094,8586444511),
  (491642,134385412813),
  (492107,131331975829),
  (495170,130493165445),
  (508258,129520020359),
  (511842,130593828743)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert7 : (hardOr7).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr8 : List Signature := [(520258,135325022853),
  (520779,135627012757),
  (557527,125966867963),
  (558041,115204152819),
  (560663,91895488443),
  (561104,122162372595),
  (573751,99428588987),
  (574265,63197142451)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert8 : (hardOr8).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr9 : List Signature := [(577328,96222044083),
  (577335,100519108539),
  (585751,126796299707),
  (586192,110892285427),
  (586265,118440066483),
  (586713,119515905523),
  (589328,128341639091),
  (627156,105129304055)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert9 : (hardOr9).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr10 : List Signature := [(627229,47153668087),
  (630292,87967260663),
  (630740,122330144759),
  (643380,27888443383),
  (690327,92579167679),
  (690841,49905139135),
  (706992,32988724671),
  (718992,109781843391)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert10 : (hardOr10).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr11 : List Signature := [(718999,126964071871),
  (759956,8556511231),
  (819803,45430341559),
  (822866,87540105143),
  (835954,26437746615),
  (847954,109551812535),
  (851538,128342294455),
  (888918,2076966903)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert11 : (hardOr11).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr12 : List Signature := [(952530,6707478463),
  (1057855,91490300799),
  (1058247,125967488383),
  (1058296,108871509631),
  (1058761,115204902015),
  (1074471,99430109695),
  (1074985,63199660543),
  (1127484,75082114815)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert12 : (hardOr12).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr13 : List Signature := [(1127876,105130182399),
  (1127932,109441935103),
  (1127949,47156449023),
  (1144100,27891992575),
  (1191047,92580821375),
  (1191096,76491405951),
  (1191103,93671340927),
  (1191561,49907923071)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert13 : (hardOr13).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr14 : List Signature := [(1207712,32992279039),
  (1260676,8560459519),
  (1287175,133244588415),
  (1287224,134385377919),
  (1287616,130224702591),
  (1287689,131331934335),
  (1288137,132405742719),
  (1303840,129519976959)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert14 : (hardOr14).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr15 : List Signature := [(1303847,133815013887),
  (1320058,74255870719),
  (1320523,45432630015),
  (1336674,26440805375),
  (1389638,2080288511),
  (1453250,6710803199),
  (1549378,128882486015),
  (1549434,134385412863)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert15 : (hardOr15).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr16 : List Signature := [(1614871,90265607679),
  (1615312,104425577983),
  (1615319,125967523327),
  (1615385,45411720703),
  (1631536,26415717887),
  (1684500,2051006463),
  (1748112,6681525759),
  (1835071,137425138542)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert16 : (hardOr16).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr17 : List Signature := [(1835463,137408894330),
  (1835512,137425938044),
  (1835977,137417149553),
  (1838599,137428834218),
  (1838648,137429100492),
  (1839040,137429633008),
  (1851687,137412153771),
  (1852201,137419442579)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert17 : (hardOr17).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr18 : List Signature := [(1855264,137426864003),
  (1863687,137433053482),
  (1863736,137433315916),
  (1864128,137433840752),
  (1864201,137431873553),
  (1867264,137434890112),
  (1877074,33554431),
  (1904700,137424807645)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert18 : (hardOr18).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr19 : List Signature := [(1905092,137408628469),
  (1905165,137414987477),
  (1905613,137417150197),
  (1908228,137426470869),
  (1921316,137409988567),
  (1924900,137426864087),
  (1968263,137407838511),
  (1968312,137424812623)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert19 : (hardOr19).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr20 : List Signature := [(1968777,137414998047),
  (1984928,137410001295),
  (1984935,137412164015),
  (1996928,137430693903),
  (1997449,137431873567),
  (2037892,137405415135),
  (2037948,137424813791),
  (2064391,137438892330)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert20 : (hardOr20).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

def hardOr21 : List Signature := [(2064440,137438831180),
  (2064832,137438905456),
  (2064905,137438840849),
  (2067968,137438922624),
  (2081056,137438822787),
  (2081577,137438841235),
  (2093056,137438951424)]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 15000000 in
lemma hardOrcert21 : (hardOr21).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by decide +kernel

lemma hardOrcert : (hardOr0 ++ hardOr1 ++ hardOr2 ++ hardOr3 ++ hardOr4 ++ hardOr5 ++ hardOr6 ++ hardOr7 ++ hardOr8 ++ hardOr9 ++ hardOr10 ++ hardOr11 ++ hardOr12 ++ hardOr13 ++ hardOr14 ++ hardOr15 ++ hardOr16 ++ hardOr17 ++ hardOr18 ++ hardOr19 ++ hardOr20 ++ hardOr21).all (fun a => excOr.all (fun b => decide (ec (either a b) < 21 ∨ 28 ≤ zc (either a b)))) = true := by
  simp only [List.all_append,hardOrcert0,hardOrcert1,hardOrcert2,hardOrcert3,hardOrcert4,hardOrcert5,hardOrcert6,hardOrcert7,hardOrcert8,hardOrcert9,hardOrcert10,hardOrcert11,hardOrcert12,hardOrcert13,hardOrcert14,hardOrcert15,hardOrcert16,hardOrcert17,hardOrcert18,hardOrcert19,hardOrcert20,hardOrcert21,Bool.and_self]

lemma two_ok {s} (h : Reach atoms 2 s) : twoOK s := by
  obtain ⟨a,b,ha,hb,h|h⟩ := h <;> subst s
  · exact test_sound _ ((Bool.and_eq_true_iff.mp (List.all_eq_true.mp
      (List.all_eq_true.mp chunkcert a (one_mem ha)) b (one_mem hb))).1)
  · exact test_sound _ ((Bool.and_eq_true_iff.mp (List.all_eq_true.mp
      (List.all_eq_true.mp chunkcert a (one_mem ha)) b (one_mem hb))).2)

lemma hard_and (a b : Signature) (ha : a ∈ excAnd) (hb : b ∈ excAnd) :
    19 ≤ Z (both a b) := by
  simpa only [zc_correct] using of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp hardAndcert a ha) b hb)

lemma hard_or (a b : Signature) (ha : a ∈ excOr) (hb : b ∈ excOr) :
    E (either a b) < 21 ∨ 28 ≤ Z (either a b) := by
  simpa only [ec_correct,zc_correct] using of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp hardOrcert a ha) b hb)

lemma three {s} (h : Reach atoms 3 s) :
    (Z s = 0 → E s ≤ 4) ∧ (21 ≤ E s → 28 ≤ Z s) ∧ (11 ≤ E s → 19 ≤ Z s) := by
  obtain ⟨a,b,ha,hb,shape⟩ := h
  obtain ⟨a12,a0,a5,a11,ah,ao⟩ := two_ok ha
  obtain ⟨b12,b0,b5,b11,bh,bo⟩ := two_ok hb
  rcases shape with rfl | rfl
  · have ep := band 21 a.1 b.1
    have en := band 37 a.2 b.2
    change E (both a b) ≤ E a ∧ E (both a b) ≤ E b ∧ E a + E b ≤ E (both a b) + 21 at ep
    change Z (both a b) ≤ Z a ∧ Z (both a b) ≤ Z b ∧ Z a + Z b ≤ Z (both a b) + 37 at en
    refine ⟨by omega,by omega,?_⟩
    intro e
    by_contra! low
    have hl := hard_and a b (ah (by omega) (by omega)) (bh (by omega) (by omega))
    omega
  · have ep := bor 21 a.1 b.1
    have en := bor 37 a.2 b.2
    change E a ≤ E (either a b) ∧ E b ≤ E (either a b) ∧ E (either a b) ≤ E a + E b at ep
    change Z a ≤ Z (either a b) ∧ Z b ≤ Z (either a b) ∧ Z (either a b) ≤ Z a + Z b at en
    refine ⟨by omega,?_,by omega⟩
    intro e
    by_contra! low
    have hl := hard_or a b (ao (by omega) (by omega)) (bo (by omega) (by omega))
    omega

lemma four {s} (h : Reach atoms 4 s) :
    (Z s = 0 → E s ≤ 10) ∧ (21 ≤ E s → 19 ≤ Z s) := by
  obtain ⟨a,b,ha,hb,shape⟩ := h
  obtain ⟨a0,a21,a11⟩ := three ha
  obtain ⟨b0,b21,b11⟩ := three hb
  rcases shape with rfl | rfl
  · have ep := band 21 a.1 b.1
    have en := band 37 a.2 b.2
    change E (both a b) ≤ E a ∧ E (both a b) ≤ E b ∧ E a + E b ≤ E (both a b) + 21 at ep
    change Z (both a b) ≤ Z a ∧ Z (both a b) ≤ Z b ∧ Z a + Z b ≤ Z (both a b) + 37 at en
    constructor <;> omega
  · have ep := bor 21 a.1 b.1
    have en := bor 37 a.2 b.2
    change E a ≤ E (either a b) ∧ E b ≤ E (either a b) ∧ E (either a b) ≤ E a + E b at ep
    change Z a ≤ Z (either a b) ∧ Z b ≤ Z (either a b) ∧ Z (either a b) ≤ Z a + Z b at en
    constructor <;> omega

theorem no_five (s : Signature) (h : Reach atoms 5 s) (p : E s = 21) (z : Z s = 0) : False := by
  obtain ⟨a,b,ha,hb,shape⟩ := h
  obtain ⟨a0,a21⟩ := four ha
  obtain ⟨b0,b21⟩ := four hb
  rcases shape with rfl | rfl
  · have ep := band 21 a.1 b.1
    have en := band 37 a.2 b.2
    change E (both a b) ≤ E a ∧ E (both a b) ≤ E b ∧ E a + E b ≤ E (both a b) + 21 at ep
    change Z (both a b) ≤ Z a ∧ Z (both a b) ≤ Z b ∧ Z a + Z b ≤ Z (both a b) + 37 at en
    omega
  · have ep := bor 21 a.1 b.1
    have en := bor 37 a.2 b.2
    change E a ≤ E (either a b) ∧ E b ≤ E (either a b) ∧ E (either a b) ≤ E a + E b at ep
    change Z a ≤ Z (either a b) ∧ Z b ≤ Z (either a b) ∧ Z (either a b) ≤ Z a + Z b at en
    omega

lemma proj : ∀ i : Fin 14, Reach atoms 0 (sig (fun x => x i)) := by
  change ∀ i : Fin 14, sig (fun x => x i) ∈ atoms
  decide +kernel

lemma close_ops (k : ℕ) (f g : V) (hf : Reach atoms k (sig f)) (hg : Reach atoms k (sig g)) :
    Reach atoms (k+1) (sig (fun x => f x && g x)) ∧ Reach atoms (k+1) (sig (fun x => f x || g x)) := by
  constructor
  · exact ⟨sig f,sig g,hf,hg,Or.inl (by simp [sig,both,enc_and])⟩
  · exact ⟨sig f,sig g,hf,hg,Or.inr (by simp [sig,either,enc_or])⟩

end PEqualNP.Outside.L_meta_1620_aux

open PEqualNP.Outside.L_meta_1620_aux

theorem PEqualNP.Outside.L_meta_1620 : ¬ (∀ T : ℕ → Set ((Fin 14 → Bool) → Bool), (∀ i : Fin 14, (fun x : Fin 14 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 14 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 14 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 14 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 14 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 14 → Bool => (z 0 && z 7) || (z 0 && z 8) || (z 0 && z 10) || (z 1 && z 7) || (z 1 && z 9) || (z 1 && z 13) || (z 2 && z 8) || (z 2 && z 12) || (z 2 && z 13) || (z 3 && z 7) || (z 3 && z 11) || (z 3 && z 12) || (z 4 && z 10) || (z 4 && z 11) || (z 4 && z 13) || (z 5 && z 9) || (z 5 && z 10) || (z 5 && z 12) || (z 6 && z 8) || (z 6 && z 9) || (z 6 && z 11)) ∈ T 5) := by
  intro universal
  have hit := universal (fun k => {f | Reach atoms k (sig f)})
    (fun i => proj i) (fun _ _ h => promote h) (fun k f g hf hg => close_ops k f g hf hg)
  exact no_five _ hit (by decide) (by decide)
