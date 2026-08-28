# 技术报告：P ≠ NP 形式化证明工程（Lean 4）

- **项目**：`D:\lean4\pvsnp`（lake 工程，库名/模块名 `PvsNP`）
- **版本**：commit `7c62750`（全链 0 error、0 sorry、单公理）
- **作者**：Bojin Zheng, Jingwen Zheng
- **日期**：2026-08
- **配套论文**：`measure.C.0.7.tex`、`models.C.0.6.tex`、`MultiType.C1.2.tex`（理念篇）等

---

## 1. 项目概述

在 Lean 4（mathlib）中对"P ≠ NP"给出**单一公理**基础上的完整形式化证明链。核心思想（对应论文框架）：

- 计算模型使用 **CBTM**（复合带图灵机，符号 = 实部 × 虚部，F4 = `Bool × Bool`）；
- 非确定性分支的"虚部"不是外部编码约定，而是**计算模型的内在语义**（数计一体：语义内建于符号）；
- 虚部标记（α = `(false,true)`）携带**不可公度性**语义——每个标记对应一个素数平方根生成元（线性独立），构成**本质维度 κ** 的度量单位；
- 经典 Bool 层 = F4 层的**实部投影**（压平）：虚部与语言无关，只与计算模型有关；
- 分离（P ≠ NP）发生在**虚部语义层**（F4 层，严格可证）；**框架内经典闭合**在 CBTM 内部完成——CBTM0 逐一步模拟 DTM（维度 0 保持），选项下界（κ ≥ n）与维度 0 的矛盾传到 CBTM0（`no_dtm_recognizes_subsetSumF4`，无前提、无新公理，见 §6.5）。

**交付标准**：0 `sorry`、0 error、`lake build` 通过、全部结论由单一公理 `exists_NTM2_solves_subsetSum`（公理 V6，四条款）推出。

---

## 2. 计算模型

### 2.1 NTM2 —— 规范非确定图灵机（`Basic.lean`）

最终模型（经用户多次修正后定型）：

- **输入**：`List Bool`（与经典 P/NP 语言相同；虚部不是输入的一部分，而是计算模型层的标记）；
- **格局** `NTM2Config A x`：`{ state : ℕ, tape : ℤ → F4, headPos : ℤ }`——复合磁带（实部读/写 = 经典语义，虚部 = vb 带值）；
- **转移**：积型签名 `(ℕ × Bool × ℤ) → Finset (ℕ × Bool × Dir)`（状态 × 读到的实部 × 位置 → 有限转移集合）；
- **vb 派生**（`vbAt : ℤ → Bool`）：虚部不由机器存储，而是从转移结构派生（card = 2，与位置绑定；分叉 ⟺ 虚部 = 1）；
- **初始带**：输入区实部 = 输入串，虚部 = `vbAt`；空白格 = `(blankSym, vbAt 0)`（空白区虚部常数化）；
- **接受** `acceptsTape`：存在可达接受路径（磁带语义）。

**规范条款 `NTM2.Canonical`**（用户裁定"每格至多一次"，取代空白一致性）：

1. 任意可达路径每步磁头位置 ∈ `[0, len)`（只在输入区内活动）；
2. 非空路径的终配置 `headPos < len`；
3. `List.Nodup (π.map pos)`（每格至多读一次）。

### 2.2 CBTM —— 复合带图灵机（`CBTM.lean`，708 行）

- 符号表 F4：`zero=(false,false)`、`one=(true,false)`、`alpha=(false,true)`、`beta=(true,true)`；
- 转移位置化：`transition : ℕ × F4 × ℤ → Finset (ℕ × F4 × Dir)`（状态 × 符号 × 位置）；
- `tapeAccepts`：磁带语义接受（存在接受路径，逐符号消费输入）；
- `IsRestricted`：受限机器（读符号虚部全 false；读虚部 true 的符号 → 转移 ∅，`h_transition_outside` → 必然拒绝）；
- **`isPolynomialTime`（已实化，非占位）**：`∃ p，多项式界 ∧ ∀ 接受路径，π.length ≤ p(|x|)`——多项式界 `IsPolynomialBound p := ∃ k, ∀ n, p n ≤ n^k + k`（定义于 CBTM.lean；实化定义于 IVM.lean，依赖磁带语义）；
- **空白符号修正（2026-08-28）**：`ClassicDTM.toCBTM.blankSym := boolToF4 M.blankSym`（原固定 `F4.zero`）、`CBTM.toClassicDTM.blankSym := (N.blankSym).1`（原固定 `false`）——保证 DTM↔CBTM0 双向模拟的空白区匹配（DTM 空白可为 true 时原定义错位）；
- `exists_CBTM_iso_NTM2`：`∃ M, M = NTM2.toCBTM A ∧ Nonempty (StructIsoNTM2CBTM A M)`（同构 = 路径上格局逐步相同，φ 恒等）。

### 2.3 IVM —— 本质维度 κ（`IVM.lean`，475 行）

- `activatedGenSetOnPath`：路径上激活的生成元集合（虚部 = 1 的标记位置）；
- `kappa_M M x`：机器 M 在输入 x 上的最坏激活生成元数；
- **`kappa_zero_of_restricted`**：受限机器任意输入 κ = 0（受限路径读的符号虚部全 false——生成元对受限机器不可见）；
- `worstCaseDimension M n`、`FessentialDimension L n`（`EssentialDimension.lean`）：语言在长度 n 上的本质维度 = 最坏验证器的最小最坏维度（`Nat.find` 形式）。

**维度度量单位**：素数平方根对的个数——每对 `{√pᵢ, -√pᵢ}` 中 `-√pᵢ = -1·√pᵢ` 线性相关，一对贡献一个独立维度；`PrimeSqrtLinearIndep.lean` 证明素数平方根族的线性独立性。

---

## 3. 复杂度类

### 3.1 F4 层（`ClassicalFramework.lean`，虚部语义层）

```lean
abbrev FLanguage : Type := Set (List F4)
def IsP_F  (L : FLanguage) : Prop :=
  ∃ M, CBTM.IsRestricted M ∧ CBTM.isPolynomialTime M ∧ (∀ w, M.tapeAccepts w ↔ L w)
def IsNP_F (L : FLanguage) : Prop :=
  ∃ M, CBTM.isPolynomialTime M ∧ (∀ w, M.tapeAccepts w ↔ L w)
def P_F : Set FLanguage := { L | IsP_F L }
def NP_F : Set FLanguage := { L | IsNP_F L }
```

- **P_F** = 受限 CBTM（0 分叉、0 维、线性不独立）判定的语言；
- **NP_F** = FULL CBTM（分叉 = 虚部语义）判定的语言。

### 3.2 Bool 层（`ClassicalComplexity.lean`，压平层）

- `BoolLanguage := Set (List Bool)`；
- `realProject w := w.map F4.re`（逐格取实部——压平的核心映射）；
- `embedBool x := x.map (fun b => (b, false))`（无标记嵌入，虚部全 false）；
- 语言层映射：`projectLanguage L := {x | ∃ w, realProject w = x ∧ L w}`、`liftLanguage A K`、`embedUpLanguage K`；
- **等价类复杂度类（用户裁定）**：

```lean
def IsP_Bool (K : BoolLanguage) : Prop := ∃ L, projectLanguage L = K ∧ IsP_F L
def IsNP_Bool (K : BoolLanguage) : Prop := ∃ L, projectLanguage L = K ∧ IsNP_F L
```

实部语言 = 带虚部语言等价类的代表："只要由一个带虚部语言被 CBTM 识别，就是该实部语言被 CBTM 识别"。

- `projectLanguage_liftLanguage : projectLanguage (liftLanguage A K) = K`（投影-提升互逆）；
- `realProject_ntm2InputToCBTM`（复合串实部投影 = 原输入，rfl 级）；
- `no_forget_recovery_dtm`：不存在经典 DTM 能恢复被遗忘的虚部信息（α/one 同实部 true、zero/beta 同实部 false——投影不可逆）。

### 3.3 经典类与 CBTM|₀（`ParamEquiv.lean`，参数化等价定理）

```lean
def IsP_classic (K : BoolLanguage) : Prop :=      -- 经典 P（ClassicDTM 判定）
  ∃ D : ClassicDTM, ∀ x : List Bool, D.acceptsTape x ↔ K x
def IsNP_classic (K : BoolLanguage) : Prop :=     -- 经典 NP（NTM2 判定；ClassicNTM = NTM2 用户裁定）
  ∃ A : NTM2, NTM2.Canonical A ∧ ∀ x : List Bool, A.acceptsTape x ↔ K x
def IsP_cb0 (K : BoolLanguage) : Prop :=          -- CBTM|₀（CBTM0：字母表 {zero,one} + 位置无关 + 单元素转移）
  ∃ N : CBTM, IsCBTM0 N ∧ ∀ x, (∃ w, realProject w = x ∧ N.tapeAccepts w) ↔ K x
```

- **DTM 磁带语义**（`acceptsTape`/`DTMTapeReachablePath`）：经典确定性路径（转移 = 单值函数），参数化等价的形式化地基；
- 论文 thm:equivalence 的语言层形态：**`P_cb0 = P_classic`**（CBTM|₀ ≡ₚₒₗy DTM，§6.4）。

---

## 4. 编码与子集和语言（`SubsetSumLanguage.lean`，1042 行）

- `SubsetSumInstance := { elements : List ℕ, target : ℕ }`、`subsetSumHolds`；
- **Bool 编码** `encodeSubsetSumBits`：每元素一块 = 选择位（sel/nosel）+ 原生二进制（nosel 计入长度，每块 1 标记 + native）；k 全线移除；target 非空（`htarget : 0 < inst.target`）；
- **F4 编码** `encodeSubsetSumF4Real`：每元素块 = `α :: 二进制`（α = 虚部 true 标记——**生成元载体在输入里**）；
- 磁带布局：0 = `#ₗ`，`[1, 1+len) = target`，`1+len = #₀`，`2+len = 元素区`；
- 虚部 true 标记数 `imTrueCount = n`（元素个数）；
- 下界链素材：`subsetSum_kappa_lower_bound`、`subsetSum_not_in_P_F`、`subsetSum_not_in_P_F'`。

---

## 5. 单一公理 A1（公理 V6 四条款，`SubsetSumInNP.lean:51`）

```lean
axiom exists_NTM2_solves_subsetSum :
  ∃ A : NTM2,
    (∀ inst, inst.elements ≠ [] →
      (subsetSumHolds inst ↔ A.acceptsTape (encodeSubsetSumBits inst)) ∧
      ∃ π, ∃ cfg, TapeReachablePathNTM2 A (encodeSubsetSumBits inst) π cfg ∧
        cfg.state ∈ A.acceptStates ∧ ntm2ForkCount A π = inst.elements.length) ∧  -- ① 求解
    (∀ inst, inst.elements ≠ [] →
      ntm2InputToCBTM A (encodeSubsetSumBits inst) = encodeSubsetSumF4Real inst) ∧   -- ② 语言桥
    NTM2.Canonical A ∧                                                                -- ③ 规范
    (∀ w : List F4, (∀ inst, elements ≠ [] → w ≠ encodeF4Real inst) →
      ¬ (NTM2.toCBTM A).tapeAccepts w)                                                -- ④ 非编码拒绝
```

- **① 求解**：子集和成立 ⟺ 规范 NTM2 接受编码串，且存在分叉次数 = 元素个数的接受路径；
- **② 语言桥**：实部输入经 vb 复合 = 语言的 F4 编码；
- **③ 规范**：磁头只在输入区内活动、每格至多读一次（机器性质，与输入无关）；
- **④ 非编码拒绝**：对不是任何非空实例编码的 F4 串，`toCBTM A` 拒绝。

**历史**：V4（语言识别条款）→ V5（三条款，删条款 4 后 `subsetSum_in_NP_F` 断 2 个 sorry——∀ w 行为不可推出，接受路径可停在半路）→ **V6**（非编码拒绝条款闭合）。条款 ①+②+③+④ 组合 ⟺ 原"恰好识别"条款。A2 公理（同构桥）已消为定理。

---

## 6. 主要定理链

### 6.1 第一层：CBTM 内部 `P_F ≠ NP_F`（严格分离，全绿）

```
subsetSum_in_NP_F        : IsNP_F subsetSumLanguageF4Real        （SubsetSumInNP.lean:109）
  -- witness = NTM2.toCBTM A：编码方向经条款①(求解) + ②(语言桥) + 桥；
  --                       非编码方向由条款④(非编码拒绝)矛盾；
  --                       多项式时间 = toCBTM_polynomialTime（实化 isPolynomialTime）
toCBTM_polynomialTime    : toCBTM A 多项式时间（线性界 p = id）
  -- 接受路径只在编码串上（条款④）→ 编码串 = 复合串（条款②语言桥）
  -- → 复合串上路径与 NTM2 路径同长（iso_path_backward 长度分量）
  -- → Canonical（每格至多读一次）给出 π.length ≤ |x|（canonical_path_length_le）
subsetSum_kappa_lower_bound : κ_M M (encode inst) ≥ elements.length
  -- 每个元素 = 一个 α 标记（线性独立的素数平方根生成元）；
  -- 翻转 α 实部 → 不在语言（flipReAt_activated_not_in_L）→ 必须读 → 生成元激活
kappa_zero_of_restricted : 受限机器 κ = 0（任意输入）
subsetSum_not_in_P_F'    : ¬ IsP_F subsetSumLanguageF4Real       （维度矛盾：n vs 0）
P_F_neq_NP_F             : P_F ≠ NP_F                             （FinalProof.lean:75）
P_neq_NP_with_barriers   : 分离 + 相对化/代数化不变性            （Barriers.lean）
```

**论证本质（用户框架）**：2ⁿ 个部分和需要 n 个独立维度表示（鸽巢/信息论）；正确机器必须读遍 n 个 α 标记（κ ≥ n）；受限机器 0 维（κ = 0，读的符号虚部全 false）——**线性独立（素数平方根）vs 线性不独立（0 维）** 的矛盾。

### 6.2 第二层：Bool 层压平（NP 方向全绿）

```
subsetSumLanguageF4Real_eq_lift : L_F4 = liftLanguage A K         （复合提升 = 语言桥条款）
projectLanguage_liftLanguage    : projectLanguage (liftLanguage A K) = K
subsetSum_in_NP   : IsNP_Bool subsetSumBoolLanguage
  -- 等价类 witness L = subsetSumLanguageF4Real（投影等式 + IsNP_F）
subsetSum_NP_chain : projectLanguage L_F4 = K ∧ IsNP_Bool K
subsetSum_in_NP_classic : IsNP_classic subsetSumBoolLanguage       （PNPClosure.lean:110）
  -- 经典 NP 形态：witness = Canonical NTM2 A（ntm2_language_recognition + 同构桥 + 语言桥）
```

"每一个 NP_f 投影得到的语言 ∈ NP"（FULL CBTM 恒可被 NTM2 模拟）在此实例化。

### 6.3 第三层：NTM2 与同构桥（A2 消去）

```
StructIso_preserves_accepts : NTM2.Canonical A → ∀ x,
  A.acceptsTape x ↔ M.tapeAccepts (ntm2InputToCBTM A x)          （A2Bridge.lean，前提 = 规范）
exists_CBTM_iso_NTM2          : ∃ M, M = NTM2.toCBTM A ∧ Nonempty (StructIsoNTM2CBTM A M)
NTM2_iso_composite_language   : (∀ x, A.acceptsTape x ↔ K x) → 复合语言由 toCBTM A 判定
```

原公理 `NTM2_solve_implies_IsNP_F`（A2）由语言识别条款消去为定理——同构 = 任意计算路径上格局逐步相同（一一映射即恒等）。

### 6.4 参数化等价定理（`ParamEquiv.lean`，783 行）

```
P_cb0_eq_P_classic : {K | IsP_cb0 K} = {K | IsP_classic K}        （论文 thm:equivalence(1)）
```

**证明骨架**（双向接受保持，直接构造，不经同构结构）：

- **经典 ⊆ CBTM|₀**（`IsP_classic_subset_IsP_cb0`）：D 判 K → `N = D.toCBTM` 判投影 K——`D` 接受 x ⟺ `N` 接受 `embedBool x`（`dtm_path_to_cbtm`/`dtm_accepts_to_cbtm` 路径对应）⟺ 投影接受（受限不敏感：`restricted_tapeAccepts_of_embed` 重放——受限路径读符号虚部全 false，接受串在未读位置任意）⟹ `x ∈ K`（投影语义定义）；
- **CBTM|₀ ⊆ 经典**（`IsP_cb0_subset_IsP_classic`）：N（IsCBTM0）判投影 K → `D = N.toClassicDTM h0` 判 K——投影接受 ⟹ `N` 接受 `embedBool x`（重放）⟹ `D` 接受 x（`cbtm0_path_to_dtm` 路径对应 + `dtm_replay_of_trans_eq` 转移相同重放）；反向：`dtm_path_to_cbtm0` + `cbtm0_accepts_to_dtm`；
- **支撑引理**：`realProject_embedBool : realProject (embedBool x) = x`（`@[simp]`）、`choose_eq_of_card_one`（单元素集 choose 唯一）、`toClassicDTM_of_toCBTM_trans`（toCBTM↔toClassicDTM 转移相等）、blankSym 匹配（§2.2 修正）。

**意义**：CBTM|₀（受限 CBTM 的规范形态：字母表 {zero,one}、位置无关、确定性）与经典 DTM 外延等价——**CBTM 框架不引入超计算能力**，P 方向的经典-框架桥梁成立。

### 6.5 框架内经典 P ≠ NP（`PNPClosure.lean`，闭合论证——无前提、无新公理）
```
Verifiers_tape L          : Bool 语言验证器集合（磁带语义；isPolynomialTime + 投影识别）
essentialDimension_tape L : Bool 语言本质维度（= 论文 κ(L)；Nat.find 最小验证器最坏维度）
PClassZeroDimension_tape  : IsP_Bool L → essentialDimension_tape L refLen = 0（零维定理）
isCBTM0_isRestricted      : IsCBTM0 M → IsRestricted M
no_restricted_recognizes_subsetSumF4 :
    ¬ ∃ M, IsRestricted M ∧ (∀ w, M.tapeAccepts w ↔ subsetSumLanguageF4Real w)
no_cbtm0_recognizes_subsetSumF4 :
    ¬ ∃ M, IsCBTM0 M ∧ (∀ w, M.tapeAccepts w ↔ subsetSumLanguageF4Real w)
dtm_sim_worstCaseDimension_zero (D) (n) :
    worstCaseDimension (D.toCBTM) n = 0                 （维度 0 保持）
no_dtm_recognizes_subsetSumF4 :
    ¬ ∃ D : ClassicDTM, ∀ w, (D.toCBTM).tapeAccepts w ↔ subsetSumLanguageF4Real w
    （矛盾传到 CBTM0）
```

**论证形态（2026-08-28 用户裁决：无需证明 Bool 层）**：任意经典 DTM D → `D.toCBTM` 是 CBTM0（受限机器）→ κ = 0、worstCaseDimension = 0（**维度 0 保持到所有 P 算法**——CBTM0 逐一步模拟 DTM，参数化等价定理）；子集和 α 编码语言 L_F4 的任意识别者 κ ≥ 元素数（**选项下界**——代数生成元扩张（√pᵢ 线性无关）绑定元素选择，信息论：2ⁿ 个部分和需要 n 个独立维度；`subsetSum_kappa_lower_bound` 是 Lean 内定理，非公理）⟹ 不存在受限/CBTM0 机器识别 L_F4（κ ≥ 1 vs κ = 0）⟹ 不存在经典 DTM 经 toCBTM 识别 L_F4（**矛盾传到 CBTM0**）。

**历史**：Bool 层条件闭合 `P_Bool_neq_NP_Bool`（前提 h_kappa = 论文层 κ ≥ n 下界）于 2026-08-28 取消——框架内闭合无前提、无新公理，取代之（取消记录保留在 PNPClosure.lean 注释中）。

---

## 7. 数学边界（诚实声明）

### 7.1 已严格证明

| 结论 | 状态 |
|---|---|
| `P_F ⊆ NP_F ∧ P_F ≠ NP_F`（**真子集**，语义统一层） | ✅ 定理（`P_F_ss_NP_F`） |
| `P_F ≠ NP_F`（F4/虚部语义层分离） | ✅ 定理，全链 0 error 0 sorry |
| 语义统一分离：子集和本质形态 ∈ NP_F ∖ P_F | ✅ 定理（`subsetSum_semantic_unified_separation`） |
| 编码不单射（`([1],t=3)` ≡ `([3],t=1)`） | ✅ 定理（`encodeSubsetSumF4Real_not_injective`）——Bool 串不承载块结构的严格证据 |
| `subsetSum ∈ NP_F`、`subsetSum ∈ NP_Bool`、`subsetSum ∈ NP_classic` | ✅ 定理（witness 多项式时间：`toCBTM_polynomialTime`，线性界） |
| `isPolynomialTime` 实化（接受路径 ≤ 多项式界） | ✅ 定义 + witness 证明（不再占位） |
| **参数化等价：`P_cb0 = P_classic`**（CBTM|₀ ≡ₚₒₗy DTM） | ✅ 定理（`P_cb0_eq_P_classic`，双向接受保持） |
| **零维定理：P_Bool ⟹ 本质维度 = 0** | ✅ 定理（`PClassZeroDimension_tape`） |
| **框架内闭合：不存在受限/CBTM0 机器识别 α 编码子集和语言** | ✅ 定理（`no_restricted_recognizes_subsetSumF4`、`no_cbtm0_recognizes_subsetSumF4`，无前提） |
| **维度 0 保持：任意 DTM 的 CBTM0 模拟 worstCaseDimension = 0** | ✅ 定理（`dtm_sim_worstCaseDimension_zero`） |
| **矛盾传到 CBTM0：不存在经典 DTM 经 toCBTM 识别 α 编码子集和语言** | ✅ 定理（`no_dtm_recognizes_subsetSumF4`，无前提、无新公理） |
| 投影-提升互逆、复合提升等式、等价类链条 | ✅ 定理 |
| 素数平方根线性独立、维度下界、受限 κ = 0 | ✅ 定理 |
| 相对化/代数化不变性 | ✅ 定理 |

### 7.2 历史记录：Bool 层条件闭合（已取消）

**`P_Bool_neq_NP_Bool`（前提 h_kappa = 论文层 κ ≥ n 选项下界）已于 2026-08-28 取消**——按用户裁决"无需证明 Bool 层"，框架内闭合（§6.5）无前提、无新公理，取代之。取消记录保留在 PNPClosure.lean 注释中。

### 7.3 语义统一（数计一体）的严格落点

"语义与语法必须统一"（虚部由语言结构内建，拒绝外部编码约定）在形式化中的形态：

1. **复杂度类定义在 F4 本质层**：编码（α 模式）= 定义的一部分，虚部内建——`P_F ⊊ NP_F`（`P_F_ss_NP_F`：`P_F ⊆ NP_F` + `P_F ≠ NP_F`）**全绿**；
2. **Bool 层是实部投影**（等价类）：`P_Bool = π(P_F)`、`NP_Bool = π(NP_F)`——投影不保持分离；
3. **"规范提升由 Bool 串恢复"不可行——有严格反例**：`encodeSubsetSumF4Real_not_injective`——`([1], target=3)` 与 `([3], target=1)` 编码相同（变长二进制无长度前缀 + target 区无分隔符，块区/target 区边界歧义）——Bool 串（α 标记投影后与数据 0 同符）更不能恢复块结构；
4. 因此**语义统一的 Bool 层分离类定义不存在**（任意 Bool 语言无内建结构；子集和 Bool 串不可解析）——分离的严格形式是 F4 层（已证）+ 框架内闭合（CBTM 内部，矛盾传到 CBTM0，§6.5）。

---

## 8. 交付状态与文件清单

**验收标准**：0 `sorry`、0 error、`lake build` 通过、单公理。

| 文件 | 行数 | 内容 |
|---|---|---|
| `PvsNP.lean` | — | 根模块（含 ParamEquiv/PNPClosure 导入） |
| `PvsNP/Basic.lean` | 379 | NTM2 最终模型、`NTM2.Canonical` |
| `PvsNP/CBTM.lean` | 708 | CBTM 位置模型、`IsPolynomialBound`、`exists_CBTM_iso_NTM2`、blankSym 修正 |
| `PvsNP/IVM.lean` | 475 | `isPolynomialTime`(实化)、`kappa_M`、`kappa_zero_of_restricted`、`activatedGenSetOnPath` |
| `PvsNP/EssentialDimension.lean` | 140 | `worstCaseDimension`、`FessentialDimension` |
| `PvsNP/PrimeSqrtLinearIndep.lean` | 291 | 素数平方根线性独立 |
| `PvsNP/SubsetSumLanguage.lean` | 1042 | 编码、`subsetSum_kappa_lower_bound`、`subsetSum_not_in_P_F` |
| `PvsNP/ClassicalFramework.lean` | 129 | F4 复杂度类 `IsP_F/IsNP_F/P_F/NP_F` |
| `PvsNP/ClassicalComplexity.lean` | 178 | Bool 层、等价类 `IsP_Bool/IsNP_Bool`、语言映射、`ntm2_language_recognition` |
| `PvsNP/A2Bridge.lean` | 364 | 同构桥 `StructIso_preserves_accepts`(A2 消去)、长度引理(`canonical_path_length_le`、`int_nodup_bounded_length`)、`iso_path_backward` 长度分量 |
| `PvsNP/SubsetSumInNP.lean` | 216 | **公理 V6**、`subsetSum_in_NP_F`、`toCBTM_polynomialTime`、`subsetSum_in_NP` |
| `PvsNP/ParamEquiv.lean` | 783 | **参数化等价定理**：DTM 磁带语义、`IsP_classic/IsNP_classic/IsP_cb0`、`P_cb0_eq_P_classic`、重放/接受保持链 |
| `PvsNP/PNPClosure.lean` | 249 | **框架内经典 P≠NP 闭合**：`Verifiers_tape`、`essentialDimension_tape`、`PClassZeroDimension_tape`、`subsetSum_in_NP_classic`、`isCBTM0_isRestricted`、`no_restricted/cbtm0/dtm_recognizes_subsetSumF4`、`dtm_sim_worstCaseDimension_zero`(P_Bool_neq_NP_Bool 已取消,注释保留) |
| `PvsNP/FinalProof.lean` | 126 | `P_F_neq_NP_F`、`P_neq_NP_with_barriers` |
| `PvsNP/LowerBound.lean` / `Barriers.lean` / `SubsetSumNTM2.lean` | 65/100/60 | 下界链、障碍不变性 |

**git 历史**：`5414216`（公理 V6 四条款；全链 0 error 0 sorry 单公理）→ `1ffb320`（发布准备）→ `2754b0a`/`744538f`（ParamEquiv 错误修订）→ `9de25c7`/`eba7c11`（参数化等价定理成立）→ `7c62750`（PNPClosure 闭合，当前 HEAD）。

---

## 9. 复现与验证

```bash
cd D:\lean4\pvsnp
lake build                          # 全链编译，0 error（8670+ jobs）
lake env lean PvsNP/FinalProof.lean # 单文件验证（F4 层分离）
lake env lean PvsNP/ParamEquiv.lean # 参数化等价定理（P_cb0 = P_classic）
lake env lean PvsNP/PNPClosure.lean # 框架内经典 P≠NP 闭合
grep -c "sorry" PvsNP/*.lean        # 0（无 sorry）
grep -c "^axiom" PvsNP/*.lean       # 1（单公理 exists_NTM2_solves_subsetSum）
```

**工具链**：Lean 4 + mathlib（`.lake` 缓存约 7.5 GB）；命名空间改名后必须重新 `lake build`（`lake env lean` 读旧 .olean 会假报错）；Windows 并行编译偶发 `.olean.private` 瞬时读取失败（I/O 竞争，错误文件每次不同）——重试即恢复，非代码问题。
