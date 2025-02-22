(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
Generated by: David Deharbe, CLEARSY
Generated on: 2019-09-09
Generator: bxml;pog;pog2smt (Atelier B)
Application: B-method
Target solver: CVC4, Z3
|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)
; Prelude
(declare-sort U 0)
(declare-fun |*i| (U U) U)
(declare-fun |+i| (U U) U)
(declare-fun |-i| (U U) U)
(declare-fun idiv (U U) U)
(declare-fun |*r| (U U) U)
(declare-fun |+r| (U U) U)
(declare-fun |-r| (U U) U)
(declare-fun rdiv (U U) U)
(declare-fun modulo (U U) U)
(declare-fun |<i| (U U) Bool)
(declare-fun |<=i| (U U) Bool)
(declare-fun |>i| (U U) Bool)
(declare-fun |>=i| (U U) Bool)
(declare-fun |<r| (U U) Bool)
(declare-fun |<=r| (U U) Bool)
(declare-fun |>r| (U U) Bool)
(declare-fun |>=r| (U U) Bool)
(declare-fun iuminus (U) U)
(declare-fun ruminus (U) U)
(declare-fun TRUE () U)
(declare-fun FALSE () U)
(assert (not (= TRUE FALSE)))
(declare-fun empty () U)
(declare-fun bool (Bool) U)
(declare-fun BOOL () U)
(declare-fun INT () U)
(declare-fun INTEGER () U)
(declare-fun NAT () U)
(declare-fun NAT1 () U)
(declare-fun NATURAL () U)
(declare-fun NATURAL1 () U)
(declare-fun FLOAT () U)
(declare-fun MaxInt () U)
(declare-fun MinInt () U)
(declare-fun |STRING| () U)
(declare-fun REAL () U)
(declare-fun set_prod (U U) U)
(declare-fun set_diff (U U) U)
(declare-fun mapplet (U U) U)
(declare-fun |**i| (U U) U)
(declare-fun |**r| (U U) U)
(declare-fun |+->| (U U) U)
(declare-fun |+->>| (U U) U)
(declare-fun |-->| (U U) U)
(declare-fun |-->>| (U U) U)
(declare-fun |<->| (U U) U)
(declare-fun |>+>| (U U) U)
(declare-fun |>->| (U U) U)
(declare-fun |>+>>| (U U) U)
(declare-fun |>->>| (U U) U)
(declare-fun |->| (U U) U)
(declare-fun interval (U U) U)
(declare-fun composition (U U) U)
(declare-fun binary_inter (U U) U)
(declare-fun restriction_head (U U) U)
(declare-fun semicolon (U U) U)
(declare-fun |<+| (U U) U)
(declare-fun |<-| (U U) U)
(declare-fun domain_subtraction (U U) U)
(declare-fun domain_restriction (U U) U)
(declare-fun |><| (U U) U)
(declare-fun parallel_product (U U) U)
(declare-fun binary_union (U U) U)
(declare-fun restriction_tail (U U) U)
(declare-fun concatenate (U U) U)
(declare-fun range_restriction (U U) U)
(declare-fun range_subtraction (U U) U)
(declare-fun image (U U) U)
(declare-fun apply (U U) U)
(declare-fun prj1 (U U) U)
(declare-fun prj2 (U U) U)
(declare-fun iterate (U U) U)
(declare-fun |const| (U U) U)
(declare-fun rank (U U) U)
(declare-fun father (U U) U)
(declare-fun subtree (U U) U)
(declare-fun arity (U U) U)
(declare-fun |+f| (U U) U)
(declare-fun |-f| (U U) U)
(declare-fun |*f| (U U) U)
(declare-fun |fdiv| (U U) U)
(declare-fun tbin (U U U) U)
(declare-fun son (U U U) U)
(declare-fun mem (U U) Bool)
(declare-fun subset (U U) Bool)
(declare-fun strict_subset (U U) Bool)
(declare-fun |<=f| (U U) Bool)
(declare-fun |<f| (U U) Bool)
(declare-fun |>=f| (U U) Bool)
(declare-fun |>f| (U U) Bool)
(declare-fun imax (U) U)
(declare-fun imin (U) U)
(declare-fun rmax (U) U)
(declare-fun rmin (U) U)
(declare-fun card (U) U)
(declare-fun dom (U) U)
(declare-fun ran (U) U)
(declare-fun POW (U) U)
(declare-fun POW1 (U) U)
(declare-fun FIN (U) U)
(declare-fun FIN1 (U) U)
(declare-fun union (U) U)
(declare-fun inter (U) U)
(declare-fun seq (U) U)
(declare-fun seq1 (U) U)
(declare-fun iseq (U) U)
(declare-fun iseq1 (U) U)
(declare-fun inverse (U) U)
(declare-fun size (U) U)
(declare-fun perm (U) U)
(declare-fun first (U) U)
(declare-fun last (U) U)
(declare-fun id (U) U)
(declare-fun closure (U) U)
(declare-fun closure1 (U) U)
(declare-fun tail (U) U)
(declare-fun front (U) U)
(declare-fun reverse (U) U)
(declare-fun rev (U) U)
(declare-fun conc (U) U)
(declare-fun succ (U) U)
(declare-fun pred (U) U)
(declare-fun rel (U) U)
(declare-fun fnc (U) U)
(declare-fun real (U) U)
(declare-fun floor (U) U)
(declare-fun ceiling (U) U)
(declare-fun tree (U) U)
(declare-fun btree (U) U)
(declare-fun top (U) U)
(declare-fun sons (U) U)
(declare-fun prefix (U) U)
(declare-fun postfix (U) U)
(declare-fun sizet (U) U)
(declare-fun mirror (U) U)
(declare-fun left (U) U)
(declare-fun right (U) U)
(declare-fun infix (U) U)
(declare-fun ubin (U) U)
(declare-fun SEQ (U) U)
(declare-fun SET (U) U)
; Opaque formulas
(declare-fun e0 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s100_100 () U)
(declare-fun g_s101_101 () U)
(declare-fun g_s102_102 () U)
(declare-fun g_s103_103 () U)
(declare-fun g_s104_105 () U)
(declare-fun g_s105_104 () U)
(declare-fun g_s106_107 () U)
(declare-fun g_s107_106 () U)
(declare-fun g_s108_108 () U)
(declare-fun g_s109_109 () U)
(declare-fun g_s11_12 () U)
(declare-fun g_s110_110 () U)
(declare-fun g_s111_111 () U)
(declare-fun g_s112_112 () U)
(declare-fun g_s113_113 () U)
(declare-fun g_s114_114 () U)
(declare-fun g_s115_115 () U)
(declare-fun g_s116_117 () U)
(declare-fun g_s117_116 () U)
(declare-fun g_s118_118 () U)
(declare-fun g_s119_119 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s120_120 () U)
(declare-fun g_s121_121 () U)
(declare-fun g_s122_122 () U)
(declare-fun g_s123_123 () U)
(declare-fun g_s124_125 () U)
(declare-fun g_s125_124 () U)
(declare-fun g_s126_127 () U)
(declare-fun g_s127_126 () U)
(declare-fun g_s128_128 () U)
(declare-fun g_s129_129 () U)
(declare-fun g_s13_14 () U)
(declare-fun g_s130_132 () U)
(declare-fun g_s131_131 () U)
(declare-fun g_s132_130 () U)
(declare-fun g_s133_133 () U)
(declare-fun g_s134_134 () U)
(declare-fun g_s135_135 () U)
(declare-fun g_s136_138 () U)
(declare-fun g_s137_137 () U)
(declare-fun g_s138_136 () U)
(declare-fun g_s139_139 () U)
(declare-fun g_s14_15 () U)
(declare-fun g_s140_140 () U)
(declare-fun g_s141_141 () U)
(declare-fun g_s142_143 () U)
(declare-fun g_s143_142 () U)
(declare-fun g_s144_144 () U)
(declare-fun g_s145_145 () U)
(declare-fun g_s146_146 () U)
(declare-fun g_s147_148 () U)
(declare-fun g_s148_147 () U)
(declare-fun g_s149_149 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s150_150 () U)
(declare-fun g_s151_152 () U)
(declare-fun g_s152_151 () U)
(declare-fun g_s153_153 () U)
(declare-fun g_s154_154 () U)
(declare-fun g_s155_156 () U)
(declare-fun g_s156_155 () U)
(declare-fun g_s157_158 () U)
(declare-fun g_s158_157 () U)
(declare-fun g_s159_160 () U)
(declare-fun g_s16_17 () U)
(declare-fun g_s160_159 () U)
(declare-fun g_s161_162 () U)
(declare-fun g_s162_161 () U)
(declare-fun g_s163_163 () U)
(declare-fun g_s164_164 () U)
(declare-fun g_s165_165 () U)
(declare-fun g_s166_166 () U)
(declare-fun g_s167_167 () U)
(declare-fun g_s168_168 () U)
(declare-fun g_s169_170 () U)
(declare-fun g_s17_18 () U)
(declare-fun g_s170_169 () U)
(declare-fun g_s171_171 () U)
(declare-fun g_s172_173 () U)
(declare-fun g_s173_172 () U)
(declare-fun g_s174_174 () U)
(declare-fun g_s175_176 () U)
(declare-fun g_s176_175 () U)
(declare-fun g_s177_179 () U)
(declare-fun g_s178_178 () U)
(declare-fun g_s179_177 () U)
(declare-fun g_s18_19 () U)
(declare-fun g_s180_180 () U)
(declare-fun g_s181_181 () U)
(declare-fun g_s182_182 () U)
(declare-fun g_s183_183 () U)
(declare-fun g_s184_184 () U)
(declare-fun g_s185_185 () U)
(declare-fun g_s186_187 () U)
(declare-fun g_s187_186 () U)
(declare-fun g_s188_188 () U)
(declare-fun g_s189_189 () U)
(declare-fun g_s19_20 () U)
(declare-fun g_s190_190 () U)
(declare-fun g_s191_191 () U)
(declare-fun g_s192_193 () U)
(declare-fun g_s193_192 () U)
(declare-fun g_s194_194 () U)
(declare-fun g_s195_195 () U)
(declare-fun g_s196_196 () U)
(declare-fun g_s197_197 () U)
(declare-fun g_s198_199 () U)
(declare-fun g_s199_198 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_21 () U)
(declare-fun g_s200_200 () U)
(declare-fun g_s201_201 () U)
(declare-fun g_s202_202 () U)
(declare-fun g_s203_203 () U)
(declare-fun g_s204_204 () U)
(declare-fun g_s205_205 () U)
(declare-fun g_s206_206 () U)
(declare-fun g_s207_207 () U)
(declare-fun g_s208_208 () U)
(declare-fun g_s209_210 () U)
(declare-fun g_s21_22 () U)
(declare-fun g_s210_209 () U)
(declare-fun g_s211_211 () U)
(declare-fun g_s212_212 () U)
(declare-fun g_s213_213 () U)
(declare-fun g_s214_214 () U)
(declare-fun g_s215_215 () U)
(declare-fun g_s216_216 () U)
(declare-fun g_s217_217 () U)
(declare-fun g_s218_218 () U)
(declare-fun g_s219_219 () U)
(declare-fun g_s22_23 () U)
(declare-fun g_s220_220 () U)
(declare-fun g_s221_221 () U)
(declare-fun g_s222_222 () U)
(declare-fun g_s223_223 () U)
(declare-fun g_s224_224 () U)
(declare-fun g_s225_225 () U)
(declare-fun g_s226_226 () U)
(declare-fun g_s227_227 () U)
(declare-fun g_s228_228 () U)
(declare-fun g_s229_229 () U)
(declare-fun g_s23_24 () U)
(declare-fun g_s230_230 () U)
(declare-fun g_s231_231 () U)
(declare-fun g_s232_232 () U)
(declare-fun g_s233_233 () U)
(declare-fun g_s234_234 () U)
(declare-fun g_s235_235 () U)
(declare-fun g_s236_236 () U)
(declare-fun g_s237_237 () U)
(declare-fun g_s238_238 () U)
(declare-fun g_s239_239 () U)
(declare-fun g_s24_25 () U)
(declare-fun g_s240_241 () U)
(declare-fun g_s241_240 () U)
(declare-fun g_s242_243 () U)
(declare-fun g_s243_242 () U)
(declare-fun g_s244_244 () U)
(declare-fun g_s245_247 () U)
(declare-fun g_s246_246 () U)
(declare-fun g_s247_245 () U)
(declare-fun g_s248_249 () U)
(declare-fun g_s249_248 () U)
(declare-fun g_s25_26 () U)
(declare-fun g_s250_251 () U)
(declare-fun g_s251_250 () U)
(declare-fun g_s252_252 () U)
(declare-fun g_s253_253 () U)
(declare-fun g_s254_254 () U)
(declare-fun g_s255_255 () U)
(declare-fun g_s256_256 () U)
(declare-fun g_s257_257 () U)
(declare-fun g_s258_258 () U)
(declare-fun g_s259_260 () U)
(declare-fun g_s26_27 () U)
(declare-fun g_s260_259 () U)
(declare-fun g_s261_261 () U)
(declare-fun g_s262_262 () U)
(declare-fun g_s263_264 () U)
(declare-fun g_s264_263 () U)
(declare-fun g_s265_265 () U)
(declare-fun g_s267_266 () U)
(declare-fun g_s268_267 () U)
(declare-fun g_s269_268 () U)
(declare-fun g_s27_28 () U)
(declare-fun g_s270_269 () U)
(declare-fun g_s271_270 () U)
(declare-fun g_s272_271 () U)
(declare-fun g_s273_272 () U)
(declare-fun g_s274_273 () U)
(declare-fun g_s275_274 () U)
(declare-fun g_s28_29 () U)
(declare-fun g_s29_30 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s30_31 () U)
(declare-fun g_s31_32 () U)
(declare-fun g_s32_33 () U)
(declare-fun g_s33_34 () U)
(declare-fun g_s34_35 () U)
(declare-fun g_s35_36 () U)
(declare-fun g_s36_37 () U)
(declare-fun g_s37_38 () U)
(declare-fun g_s38_40 () U)
(declare-fun g_s39_39 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_42 () U)
(declare-fun g_s41_41 () U)
(declare-fun g_s42_44 () U)
(declare-fun g_s43_43 () U)
(declare-fun g_s44_45 () U)
(declare-fun g_s46_46 () U)
(declare-fun g_s47_47 () U)
(declare-fun g_s48_48 () U)
(declare-fun g_s49_50 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_49 () U)
(declare-fun g_s51_51 () U)
(declare-fun g_s52_52 () U)
(declare-fun g_s53_54 () U)
(declare-fun g_s54_53 () U)
(declare-fun g_s55_56 () U)
(declare-fun g_s56_55 () U)
(declare-fun g_s57_58 () U)
(declare-fun g_s58_57 () U)
(declare-fun g_s59_60 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_59 () U)
(declare-fun g_s61_62 () U)
(declare-fun g_s62_61 () U)
(declare-fun g_s63_64 () U)
(declare-fun g_s64_63 () U)
(declare-fun g_s65_66 () U)
(declare-fun g_s66_65 () U)
(declare-fun g_s67_67 () U)
(declare-fun g_s68_68 () U)
(declare-fun g_s69_69 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_71 () U)
(declare-fun g_s71_70 () U)
(declare-fun g_s72_72 () U)
(declare-fun g_s73_73 () U)
(declare-fun g_s74_74 () U)
(declare-fun g_s75_76 () U)
(declare-fun g_s76_75 () U)
(declare-fun g_s77_77 () U)
(declare-fun g_s78_78 () U)
(declare-fun g_s79_79 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_80 () U)
(declare-fun g_s81_81 () U)
(declare-fun g_s82_83 () U)
(declare-fun g_s83_82 () U)
(declare-fun g_s84_85 () U)
(declare-fun g_s85_84 () U)
(declare-fun g_s86_87 () U)
(declare-fun g_s87_86 () U)
(declare-fun g_s88_89 () U)
(declare-fun g_s89_88 () U)
(declare-fun g_s9_10 () U)
(declare-fun g_s90_91 () U)
(declare-fun g_s91_90 () U)
(declare-fun g_s92_92 () U)
(declare-fun g_s93_93 () U)
(declare-fun g_s94_94 () U)
(declare-fun g_s95_95 () U)
(declare-fun g_s96_97 () U)
(declare-fun g_s97_96 () U)
(declare-fun g_s98_98 () U)
(declare-fun g_s99_99 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (not (= g_s0_1 empty)) (not (= g_s1_2 empty)) (not (= g_s2_3 empty)) (= g_s3_4 (SET (mapplet g_s6_7 (mapplet g_s5_6 g_s4_5)))) (not (= g_s7_8 empty)) (not (= g_s8_9 empty)) (subset g_s9_10 g_s0_1) (mem g_s10_11 g_s0_1) (not (mem g_s10_11 g_s9_10)) (mem g_s11_12 (|+->| NAT g_s0_1)) (mem g_s11_12 (perm g_s9_10)) (subset g_s12_13 g_s1_2) (mem g_s13_14 g_s1_2) (not (mem g_s13_14 g_s12_13)) (mem g_s14_15 (|+->| NAT g_s1_2)) (mem g_s14_15 (perm g_s12_13)) (subset g_s15_16 g_s2_3) (mem g_s16_17 g_s2_3) (not (mem g_s16_17 g_s15_16)) (mem g_s17_18 (|+->| NAT g_s2_3)) (mem g_s17_18 (perm g_s15_16)) (subset g_s18_19 g_s7_8) (mem g_s19_20 g_s7_8) (not (mem g_s19_20 g_s18_19)) (mem g_s20_21 (|+->| NAT g_s7_8)) (mem g_s20_21 (perm g_s18_19)) (subset g_s21_22 g_s8_9) (mem g_s22_23 g_s8_9) (not (mem g_s22_23 g_s21_22)) (mem g_s23_24 (|+->| NAT g_s8_9)) (mem g_s23_24 (perm g_s21_22)) (mem g_s24_25 BOOL) (mem g_s25_26 BOOL) (mem g_s26_27 BOOL) (mem g_s27_28 BOOL) (mem g_s28_29 BOOL) (mem g_s29_30 BOOL) (mem g_s30_31 BOOL) (mem g_s31_32 BOOL) (mem g_s32_33 BOOL) (subset g_s33_34 g_s9_10) (subset g_s34_35 g_s9_10) (subset g_s35_36 g_s9_10) (subset g_s36_37 g_s9_10) (subset g_s37_38 g_s9_10) (mem g_s38_40 (|+->| g_s9_10 g_s39_39)) (mem g_s40_42 (|<->| g_s9_10 g_s41_41)) (mem g_s42_44 (|-->| g_s9_10 (POW g_s43_43))) (mem g_s44_45 (seq g_s41_41)) (forall ((l_s45 U)) (=> (mem l_s45 g_s9_10) (= (image g_s40_42 (SET l_s45)) (image g_s44_45 (apply g_s42_44 l_s45))))) (forall ((l_s45 U)) (=> (mem l_s45 g_s9_10) (subset (apply g_s42_44 l_s45) (dom g_s44_45)))) (forall ((l_s45 U)) (=> (mem l_s45 g_s9_10) (mem (domain_restriction (apply g_s42_44 l_s45) g_s44_45) (|>+>| NATURAL g_s41_41)))) (forall ((l_s45 U)) (=> (and (mem l_s45 g_s9_10) (not (= (apply g_s42_44 l_s45) empty))) (= (apply g_s42_44 l_s45) (interval (imin (apply g_s42_44 l_s45)) (imax (apply g_s42_44 l_s45)))))) (mem g_s46_46 (|<->| g_s9_10 g_s41_41)) (mem g_s47_47 (|-->| g_s9_10 (POW g_s43_43))) (mem g_s48_48 (seq g_s41_41)) (forall ((l_s45 U)) (=> (mem l_s45 g_s9_10) (= (image g_s46_46 (SET l_s45)) (image g_s48_48 (apply g_s47_47 l_s45))))) (forall ((l_s45 U)) (=> (mem l_s45 g_s9_10) (subset (apply g_s47_47 l_s45) (dom g_s48_48)))) (forall ((l_s45 U)) (=> (mem l_s45 g_s9_10) (mem (domain_restriction (apply g_s47_47 l_s45) g_s48_48) (|>+>| NATURAL g_s41_41)))) (forall ((l_s45 U)) (=> (and (mem l_s45 g_s9_10) (not (= (apply g_s47_47 l_s45) empty))) (= (apply g_s47_47 l_s45) (interval (imin (apply g_s47_47 l_s45)) (imax (apply g_s47_47 l_s45)))))) (mem g_s49_50 (|<->| g_s9_10 g_s50_49)) (mem g_s51_51 (|-->| g_s9_10 (POW g_s43_43))) (mem g_s52_52 (seq g_s50_49)) (forall ((l_s45 U)) (=> (mem l_s45 g_s9_10) (= (image g_s49_50 (SET l_s45)) (image g_s52_52 (apply g_s51_51 l_s45))))) (forall ((l_s45 U)) (=> (mem l_s45 g_s9_10) (subset (apply g_s51_51 l_s45) (dom g_s52_52)))) (forall ((l_s45 U)) (=> (mem l_s45 g_s9_10) (mem (domain_restriction (apply g_s51_51 l_s45) g_s52_52) (|>+>| NATURAL g_s50_49)))) (forall ((l_s45 U)) (=> (and (mem l_s45 g_s9_10) (not (= (apply g_s51_51 l_s45) empty))) (= (apply g_s51_51 l_s45) (interval (imin (apply g_s51_51 l_s45)) (imax (apply g_s51_51 l_s45))))))))
(define-fun |def_seext| () Bool (and (mem g_s53_54 g_s54_53) (mem g_s55_56 (|+->| g_s56_55 g_s54_53)) (mem g_s57_58 g_s58_57) (mem g_s59_60 g_s60_59) (mem g_s61_62 g_s62_61) (mem g_s63_64 g_s64_63) (mem g_s65_66 g_s66_65) (mem g_s67_67 g_s64_63) (mem g_s68_68 g_s64_63) (mem g_s69_69 (|-->| g_s39_39 g_s66_65)) (subset g_s70_71 g_s71_70) (subset g_s72_72 g_s71_70) (mem g_s73_73 BOOL) (mem g_s74_74 BOOL) (mem g_s75_76 (|>+>| g_s56_55 g_s76_75)) (subset g_s77_77 g_s56_55) (subset g_s78_78 g_s56_55) (subset g_s79_79 g_s56_55) (subset g_s80_80 g_s56_55) (mem g_s81_81 (|+->| g_s56_55 g_s54_53)) (mem g_s82_83 (|+->| g_s56_55 g_s83_82)) (mem g_s84_85 (|+->| g_s56_55 g_s85_84)) (mem g_s86_87 (|+->| g_s56_55 g_s87_86)) (mem g_s88_89 (|+->| g_s56_55 g_s89_88)) (mem g_s90_91 (|+->| g_s56_55 g_s91_90)) (subset g_s92_92 g_s56_55) (mem g_s93_93 (|+->| g_s56_55 g_s85_84)) (mem g_s94_94 (|+->| g_s56_55 g_s87_86)) (mem g_s95_95 (|+->| g_s56_55 g_s41_41)) (mem g_s96_97 (|-->| g_s56_55 g_s97_96)) (mem g_s98_98 (|+->| g_s56_55 g_s85_84)) (mem g_s99_99 (|+->| g_s56_55 g_s87_86)) (mem g_s100_100 (|+->| g_s56_55 g_s41_41)) (mem g_s101_101 (|-->| g_s56_55 g_s97_96)) (mem g_s102_102 (|+->| g_s56_55 g_s91_90)) (subset g_s103_103 g_s56_55) (mem g_s104_105 (|+->| g_s56_55 g_s105_104)) (mem g_s106_107 (|+->| g_s56_55 g_s107_106)) (subset g_s108_108 g_s56_55) (subset g_s109_109 g_s56_55) (subset g_s110_110 g_s56_55) (subset g_s111_111 g_s56_55) (subset g_s112_112 g_s56_55) (subset g_s113_113 g_s56_55) (subset g_s114_114 g_s56_55) (subset g_s115_115 g_s56_55) (mem g_s116_117 (|+->| g_s56_55 g_s117_116)) (subset g_s118_118 g_s56_55) (subset g_s119_119 g_s56_55) (subset g_s120_120 g_s56_55) (mem g_s121_121 (|+->| g_s56_55 g_s54_53)) (mem g_s122_122 (|+->| g_s56_55 g_s54_53)) (subset g_s123_123 g_s56_55) (mem g_s124_125 (|+->| g_s125_124 g_s91_90)) (mem g_s126_127 (|+->| g_s127_126 g_s54_53)) (mem g_s128_128 (|+->| g_s125_124 g_s54_53)) (mem g_s129_129 (|+->| g_s127_126 g_s54_53)) (mem g_s130_132 (|-->| g_s131_131 (POW g_s132_130))) (mem g_s133_133 (|+->| g_s131_131 g_s54_53)) (subset g_s134_134 g_s131_131) (mem g_s135_135 (|+->| g_s131_131 g_s54_53)) (mem g_s136_138 (|-->| g_s131_131 (|+->| g_s137_137 g_s138_136))) (mem g_s139_139 (|-->| g_s131_131 (POW g_s137_137))) (mem g_s140_140 (|+->| g_s131_131 g_s54_53)) (subset g_s141_141 g_s131_131) (mem g_s142_143 g_s143_142) (mem g_s144_144 g_s143_142) (mem g_s145_145 g_s143_142) (mem g_s146_146 g_s143_142) (mem g_s147_148 g_s148_147) (mem g_s149_149 g_s148_147) (mem g_s150_150 g_s148_147) (mem g_s151_152 g_s152_151) (mem g_s153_153 g_s148_147) (mem g_s154_154 g_s152_151) (mem g_s155_156 g_s156_155) (mem g_s157_158 g_s158_157) (mem g_s159_160 g_s160_159) (mem g_s161_162 g_s162_161) (mem g_s163_163 g_s162_161) (mem g_s164_164 g_s156_155) (mem g_s165_165 g_s158_157) (mem g_s166_166 g_s160_159) (mem g_s167_167 g_s162_161) (mem g_s168_168 g_s162_161) (mem g_s169_170 g_s170_169) (mem g_s171_171 g_s170_169) (subset g_s172_173 g_s173_172) (subset g_s174_174 g_s173_172) (mem g_s175_176 (|+->| g_s173_172 g_s176_175)) (= (dom g_s93_93) (dom g_s94_94)) (= (dom g_s93_93) (dom g_s95_95)) (subset (dom g_s93_93) (dom g_s116_117)) (subset (dom g_s93_93) (dom g_s104_105)) (subset (dom g_s95_95) (dom g_s100_100)) (subset (dom g_s102_102) (dom g_s98_98)) (= (dom g_s98_98) (dom g_s99_99)) (= (dom g_s98_98) (dom g_s100_100)) (= (dom g_s98_98) (dom g_s116_117)) (= (dom g_s98_98) (dom g_s104_105)) (= (dom g_s100_100) (dom g_s121_121)) (mem g_s177_179 (|-->| g_s178_178 g_s179_177)) (mem g_s180_180 (|-->| g_s178_178 g_s54_53)) (subset g_s181_181 g_s9_10) (mem g_s182_182 (|+->| g_s9_10 g_s54_53)) (subset g_s183_183 g_s9_10) (mem g_s184_184 (|+->| g_s9_10 g_s54_53)) (mem g_s185_185 (|+->| g_s9_10 g_s54_53)) (subset g_s186_187 g_s187_186) (subset g_s188_188 g_s187_186) (mem g_s189_189 (|+->| g_s187_186 g_s54_53)) (subset g_s190_190 g_s83_82) (subset g_s191_191 g_s83_82) (subset g_s192_193 g_s193_192) (mem g_s194_194 (|+->| g_s83_82 g_s54_53)) (mem g_s195_195 (|+->| g_s83_82 g_s54_53)) (mem g_s196_196 (|+->| g_s193_192 g_s54_53)) (mem g_s197_197 (|+->| g_s193_192 g_s54_53)) (subset g_s198_199 g_s199_198) (subset g_s200_200 g_s199_198) (subset g_s201_201 g_s199_198) (subset g_s202_202 g_s199_198) (subset g_s203_203 g_s12_13) (subset g_s204_204 g_s12_13) (subset g_s205_205 g_s12_13) (subset g_s206_206 g_s9_10) (subset g_s207_207 g_s41_41) (subset g_s208_208 g_s41_41) (subset g_s209_210 g_s210_209) (subset g_s211_211 g_s210_209) (subset g_s212_212 g_s210_209) (subset g_s213_213 g_s210_209) (subset g_s214_214 g_s193_192) (subset g_s215_215 g_s193_192) (subset g_s216_216 g_s83_82) (subset g_s217_217 g_s193_192) (subset g_s218_218 g_s199_198) (subset g_s219_219 g_s199_198) (subset g_s220_220 g_s199_198) (subset g_s221_221 g_s199_198) (subset g_s222_222 g_s199_198) (subset g_s223_223 (set_prod g_s199_198 g_s91_90)) (subset g_s224_224 (set_prod g_s199_198 g_s91_90)) (subset g_s225_225 (set_prod g_s199_198 g_s91_90)) (subset g_s226_226 g_s199_198) (subset g_s227_227 g_s9_10) (mem g_s228_228 (|-->| g_s15_16 g_s3_4)) (subset g_s229_229 g_s56_55) (subset g_s230_230 g_s56_55) (subset g_s231_231 g_s56_55) (subset g_s232_232 g_s56_55) (subset g_s233_233 g_s56_55) (subset g_s234_234 g_s199_198) (subset g_s235_235 g_s199_198) (subset g_s236_236 g_s199_198) (subset g_s237_237 g_s199_198) (subset g_s238_238 g_s199_198) (subset g_s239_239 g_s199_198) (mem g_s240_241 g_s241_240) (mem g_s242_243 g_s243_242) (mem g_s244_244 BOOL) (mem g_s245_247 (|+->| g_s246_246 g_s247_245)) (mem g_s248_249 (|+->| g_s246_246 g_s249_248)) (mem g_s250_251 (|+->| g_s246_246 g_s251_250)) (mem g_s252_252 (|+->| g_s246_246 g_s251_250)) (mem g_s253_253 (|-->| g_s39_39 (|+->| g_s246_246 g_s247_245))) (mem g_s254_254 (|-->| g_s39_39 (|+->| g_s246_246 g_s249_248))) (mem g_s255_255 (|-->| g_s39_39 (|+->| g_s246_246 g_s251_250))) (mem g_s256_256 (|-->| g_s39_39 (|+->| g_s246_246 g_s251_250))) (mem g_s257_257 BOOL) (mem g_s258_258 g_s58_57) (mem g_s259_260 (|+->| g_s260_259 g_s54_53)) (subset g_s261_261 g_s9_10) (subset g_s262_262 g_s173_172) (mem g_s263_264 (|-->| g_s173_172 g_s264_263)) (mem g_s265_265 (|+->| g_s173_172 g_s176_175)) (= (dom g_s245_247) (dom g_s248_249)) (= (dom g_s245_247) (dom g_s250_251)) (= (dom g_s245_247) (dom g_s252_252)) (forall ((l_s266 U)) (=> (mem l_s266 g_s39_39) (and (= (dom (apply g_s254_254 l_s266)) (dom (apply g_s253_253 l_s266))) (= (dom (apply g_s255_255 l_s266)) (dom (apply g_s253_253 l_s266))) (= (dom (apply g_s256_256 l_s266)) (dom (apply g_s253_253 l_s266)))))) (subset g_s267_266 g_s9_10) (subset g_s268_267 g_s187_186)))
(define-fun |def_lprp| () Bool true)
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool (and (subset g_s269_268 g_s9_10) (subset g_s270_269 g_s18_19) (subset g_s271_270 g_s12_13) (subset g_s272_271 g_s18_19) (subset g_s273_272 g_s18_19) (subset g_s274_273 g_s21_22) (subset g_s275_274 g_s18_19)))
(define-fun |def_ass| () Bool true)
(define-fun |def_cst| () Bool true)
(define-fun |def_sets| () Bool true)
; PO group 0 
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_inv|)
(assert |def_ass|)
(define-fun lh_1 () Bool (= g_s30_31 TRUE))
; PO 1 in group 0
(assert (not (=> lh_1 (subset g_s9_10 g_s9_10))))
(check-sat)
(exit)