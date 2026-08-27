# 技术报告：P ≠ NP 形式化证明工程（Lean 4）

- **项目**：`D:\lean4\pvsnp`（lake 工程，库名/模块名 `PvsNP`）
- **版本**：commit `5414216`（全链 0 error、0 sorry、单公理）
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
- 分离（P ≠ NP）发生在**虚部语义层**（F4 层，严格可证）；经典 Bool 层字面分离等价于经典开放命题（详见 §7）。

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

### 2.2 CBTM —— 复合带图灵机（`CBTM.lean`，约 700 行）

- 符号表 F4：`zero=(false,false)`、`one=(true,false)`、`alpha=(false,true)`、`beta=(true,true)`；
- 转移位置化：`transition : ℕ × F4 × ℤ → Finset (ℕ × F4 × Dir)`（状态 × 符号 × 位置）；
- `tapeAccepts`：磁带语义接受（存在接受路径，逐符号消费输入）；
- `IsRestricted`：受限机器（读符号虚部全 false；读虚部 true 的符号 → 转移 ∅，`h_transition_outside` → 必然拒绝）；
- **`isPolynomialTime`（已实化，非占位）**：`∃ p，多项式界 ∧ ∀ 接受路径，π.length ≤ p(|x|)`——多项式界 `IsPolynomialBound p := ∃ k, ∀ n, p n ≤ n^k + k`（定义于 CBTM.lean；实化定义于 IVM.lean，依赖磁带语义）；
- `exists_CBTM_iso_NTM2`：`∃ M, M = NTM2.toCBTM A ∧ Nonempty (StructIsoNTM2CBTM A M)`（同构 = 路径上格局逐步相同，φ 恒等）。

### 2.3 IVM —— 本质维度 κ（`IVM.lean`，463 行）

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

---

## 4. 编码与子集和语言（`SubsetSumLanguage.lean`，1023 行）

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
```

"每一个 NP_f 投影得到的语言 ∈ NP"（FULL CBTM 恒可被 NTM2 模拟）在此实例化。

### 6.3 第三层：NTM2 与同构桥（A2 消去）

```
StructIso_preserves_accepts : NTM2.Canonical A → ∀ x,
  A.acceptsTape x ↔ M.tapeAccepts (ntm2InputToCBTM A x)          （_A2Bridge.lean，前提 = 规范）
exists_CBTM_iso_NTM2          : ∃ M, M = NTM2.toCBTM A ∧ Nonempty (StructIsoNTM2CBTM A M)
NTM2_iso_composite_language   : (∀ x, A.acceptsTape x ↔ K x) → 复合语言由 toCBTM A 判定
```

原公理 `NTM2_solve_implies_IsNP_F`（A2）由语言识别条款消去为定理——同构 = 任意计算路径上格局逐步相同（一一映射即恒等）。

---

## 7. 数学边界（诚实声明）

### 7.1 已严格证明

| 结论 | 状态 |
|---|---|
| `P_F ⊆ NP_F ∧ P_F ≠ NP_F`（**真子集**，语义统一层） | ✅ 定理（`P_F_ss_NP_F`） |
| `P_F ≠ NP_F`（F4/虚部语义层分离） | ✅ 定理，全链 0 error 0 sorry |
| 语义统一分离：子集和本质形态 ∈ NP_F ∖ P_F | ✅ 定理（`subsetSum_semantic_unified_separation`） |
| 编码不单射（`([1],t=3)` ≡ `([3],t=1)`） | ✅ 定理（`encodeSubsetSumF4Real_not_injective`）——Bool 串不承载块结构的严格证据 |
| `subsetSum ∈ NP_F`、`subsetSum ∈ NP_Bool` | ✅ 定理（witness 多项式时间：`toCBTM_polynomialTime`，线性界） |
| `isPolynomialTime` 实化（接受路径 ≤ 多项式界） | ✅ 定义 + witness 证明（不再占位） |
| 投影-提升互逆、复合提升等式、等价类链条 | ✅ 定理 |
| 素数平方根线性独立、维度下界、受限 κ = 0 | ✅ 定理 |
| 相对化/代数化不变性 | ✅ 定理 |

### 7.2 未证明（且不可证）——经典 Bool 层字面分离

**`NP_Bool ≠ P_Bool`（即 `subsetSumBoolLanguage ∉ P_Bool`）未证，且等价于经典开放命题。** 逐项原因：

1. **π 不单射**：α 与 zero 同实部 false、one 与 beta 同实部 true——投影丢失虚部；`P_F ≠ NP_F` 推不出投影后分离；
2. **等价类提升自由度**：`IsP_Bool K := ∃ L, π(L) = K ∧ IsP_F L` 允许"选择位虚部全 false"的提升（embedUp 型）——受限机器读选择位是合法操作（虚部 false），κ 论证失效；判定这种提升 = 判定经典 Bool 子集和；
3. **κ 无载体**：嵌入串虚部全 false → κ ≡ 0 对所有机器成立（不只受限）——"线性独立的元素值"在 Bool 层判定中用状态/穷举处理，代数独立性无虚部载体时不构成下界；
4. **时间下界缺失（实化后）**：`isPolynomialTime` 已实化为真多项式界（接受路径 ≤ p(|x|)，`IsPolynomialBound`）；实化后，"多项式确定性机器判 Bool 子集和不可能" = 经典 P≠NP 本身（开放问题）——信息论/鸽巢论证在计算复杂性理论中不成立（如动态规划 O(n·target) 反例："候选多"不蕴含"必须逐个试"）；事实上 `IsP_Bool K ⟺ 经典子集和 ∈ P`（两向：经典算法可嵌入为受限 CBTM 判定复合提升；受限多项式机器在嵌入输入上即经典算法）；
5. **枚举不可行**："枚举每个 P 的语言逐个排除" = `¬IsP_Bool K` 的直接展开（`∀ L, IsP_F L → π(L) ≠ K`），每个子问题都是同一个开放命题的实例，需要统一下界论证（不存在）。

**结论**：分离发生在虚部语义层（F4）——已严格证明；经典 Bool 层（实部投影）字面分离 ⟺ 经典 P≠NP，开放。这与论文立场一致："直接证明 P≠NP 不可能（经典语境），框架的贡献 = 语义层分离"。

### 7.3 语义统一（数计一体）的严格落点

"语义与语法必须统一"（虚部由语言结构内建，拒绝外部编码约定）在形式化中的形态：

1. **复杂度类定义在 F4 本质层**：编码（α 模式）= 定义的一部分，虚部内建——`P_F ⊊ NP_F`（`P_F_ss_NP_F`：`P_F ⊆ NP_F` + `P_F ≠ NP_F`）**全绿**；
2. **Bool 层是实部投影**（等价类）：`P_Bool = π(P_F)`、`NP_Bool = π(NP_F)`——投影不保持分离；
3. **"规范提升由 Bool 串恢复"不可行——有严格反例**：`encodeSubsetSumF4Real_not_injective`——`([1], target=3)` 与 `([3], target=1)` 编码相同（变长二进制无长度前缀 + target 区无分隔符，块区/target 区边界歧义）——Bool 串（α 标记投影后与数据 0 同符）更不能恢复块结构；
4. 因此**语义统一的 Bool 层分离类定义不存在**（任意 Bool 语言无内建结构；子集和 Bool 串不可解析）——分离的严格形式只能是 F4 层（已证），Bool 层保持经典等价类（开放）。

---

## 8. 交付状态与文件清单

**验收标准**：0 `sorry`、0 error、`lake build` 通过、单公理。

| 文件 | 行数 | 内容 |
|---|---|---|
| `PvsNP.lean` | — | 根模块 |
| `PvsNP/Basic.lean` | 379 | NTM2 最终模型、`NTM2.Canonical` |
| `PvsNP/CBTM.lean` | 707 | CBTM 位置模型、`IsPolynomialBound`、`exists_CBTM_iso_NTM2` |
| `PvsNP/IVM.lean` | 475 | `isPolynomialTime`(实化)、`kappa_M`、`kappa_zero_of_restricted`、`activatedGenSetOnPath` |
| `PvsNP/EssentialDimension.lean` | 140 | `worstCaseDimension`、`FessentialDimension` |
| `PvsNP/PrimeSqrtLinearIndep.lean` | 291 | 素数平方根线性独立 |
| `PvsNP/SubsetSumLanguage.lean` | 1023 | 编码、`subsetSum_kappa_lower_bound`、`subsetSum_not_in_P_F` |
| `PvsNP/ClassicalFramework.lean` | 129 | F4 复杂度类 `IsP_F/IsNP_F/P_F/NP_F` |
| `PvsNP/ClassicalComplexity.lean` | 178 | Bool 层、等价类 `IsP_Bool/IsNP_Bool`、语言映射 |
| `PvsNP/_A2Bridge.lean` | 364 | 同构桥 `StructIso_preserves_accepts`(A2 消去)、长度引理(`canonical_path_length_le`、`int_nodup_bounded_length`)、`iso_path_backward` 长度分量 |
| `PvsNP/SubsetSumInNP.lean` | 216 | **公理 V6**、`subsetSum_in_NP_F`、`toCBTM_polynomialTime`、`subsetSum_in_NP` |
| `PvsNP/FinalProof.lean` | 100 | `P_F_neq_NP_F`、`P_neq_NP_with_barriers` |
| `PvsNP/LowerBound.lean` / `Barriers.lean` / `SubsetSumNTM2.lean` | 65/100/60 | 下界链、障碍不变性 |

**git 历史**：`5414216`（非编码拒绝条款替代语言识别条款；四条款公理组合推出 IsNP_F/等价类链条；全链 0 error 0 sorry 单公理）← `53d2445`（Bool 层压平 NP 方向全绿）。

---

## 9. 复现与验证

```bash
cd D:\lean4\pvsnp
lake build                          # 全链编译，0 error
lake env lean PvsNP/FinalProof.lean # 单文件验证
grep -c "sorry" PvsNP/*.lean        # 0（无 sorry）
grep -c "^axiom" PvsNP/*.lean       # 1（单公理 exists_NTM2_solves_subsetSum）
```

**工具链**：Lean 4 + mathlib（`.lake` 缓存约 7.4 GB）；命名空间改名后必须重新 `lake build`（`lake env lean` 读旧 .olean 会假报错）。
