# Spec.md — P vs NP 形式化验证项目软件规格说明书

- **版本**：V1.0
- **日期**：2026-08-26
- **位置**：D:\lean4\mp\Spec.md
- **用途**：本文档是用户与助手之间关于本项目各项事项的**约定总纲**。凡项目中出现歧义、冲突或需要裁决之处，一律以本文档（含其版本演进）为准；文档不涉及的，再行补充约定并升版。

---

## 1. 软件的目的

在 **Lean 4**（v4.32.x，lake 工程 `D:\lean4\mp`）中，对 **P ≠ NP 的证明** 做**完全形式化验证**：

- 把证明的全部推理链（从基本定义、编码、转移表，到主定理）写成 Lean 的 `def`/`lemma`/`theorem`；
- 最终目标：**0 sorry、0 error，`lake build` 全链通过**；
- 主定理形态：`subsetSum_in_NP_F` 从公理变定理，并组装出 P ≠ NP 的主定理。

---

## 2. P vs NP 证明的简要介绍

> （约定 V1.0）本证明基于用户的 **CBTM / IVM / 数计一体** 框架，要点如下：

1. **CBTM**（Choice-Based Turing Machine）：一台图灵机，其磁带上元素区的分支符号 α/β 触发**真实双分支**（写 sel 或写 nosel）。
2. **IVM**（虚部机制）：每个分支方向对应一个"虚部"代数对象 √p_i。不激活路径（T^Im=0）停留在基域 ℚ；激活路径（T^Im=1）进入扩域 ℚ(√p_i)。两者之差 √p_i ∉ ℚ 即"不可公度性的分离"。
3. **本质维度 κ**：度量单位是**素数平方根对的个数**（每对 {√p_i, −√p_i} 中 −√p_i = −1·√p_i 线性相关，一对贡献一个独立维度）。
4. **P = NP 反证**：判定 P = NP 的机器是**本质 0 维**的（省分叉 = 省维度，恒在 ℚ）；而 NP 完备问题（如子集和）的验证需要 **Ω(n) 维**的分叉。维度 0 与 Ω(n) 的矛盾推出 P ≠ NP。
5. **三层堵死"聪明算法"**：信息论层 + 语义资源层 + 代数独立性层。BGS 相对化定理 = 语义外包（oracle），不构成障碍。
6. **完备 witness**：sel/nosel 序列（非确定路径的实际写入，可由 `scanSelPrefix` 从磁带读回）。

---

## 3. 形式化验证的概念性模块（从证明到项目的过渡）

| 概念模块 | 说明 | 对应项目实体 |
|---|---|---|
| C1 符号与编码 | Sym = SymKind × Bool（4F4 语义），符号层编码（target/元素/物理/逻辑） | `Sym`、`SymKind`、`encodeBitsSym`、`encodeElementsSym`、`encodeElementsSymWithSel`、`encodeElementsSymChosen` |
| C2 转移表 | 完整转移函数（35 个合法状态集合，表外归 101） | `VerifierSym.transition`、`legalStates` |
| C3 路径与步进 | 非确定路径 π、步进配置、SymSteps | `SymConfig`、`SymStep`、`SymSteps`、`symStepConfig` |
| C4 分支阶段 | 状态 0→1→2（α/β 双分支写 sel/nosel）→3→24→4 | `branch_phase`、`branch_phase_correct`、`branch_with_sel` |
| C5 主循环 | 状态 4→22：逐元素 subtract/clear，target 区累积减到 subAllSelected | `main_loop_correct`（Core2） |
| C6 逆方向（可靠性） | Reverse/Reverse2：从接受路径读回 witness | `SubsetSumVerifierReverse*.lean` |
| C7 NP 归约与主定理 | 子集和 ∈ NP、P ≠ NP 组装 | `SubsetSumInNP`、`FinalProof` |
| C8 CBTM/IVM 数学层 | 虚部、维度、独立性的数学形式化 | `CBTM*.lean`、`IVM`、`EssentialDimension`、`PrimeSqrtLinearIndep`、`LowerBound` |

---

## 4. 形式化验证的具体模块（精确到定义/引理/定理）

> 文件名与实体名以当前源码为准；本节列的是**主干**。

### 4.1 Mp/SubsetSumVerifierCore.lean（已绿）
- `SymKind`（9 逻辑符号）、`Sym = SymKind × Bool`
- `legalStates : Finset ℕ`（35 个显式状态；表外全归 101）——**V1.0**
- `VerifierSym.transition : ℕ × Sym → Finset SymTransResult`（外层 `if q ∈ legalStates`）——**V1.0**
- `encodeBitsSym (n) : List Sym`（target 可变长原生 digits）——**V1.0**
- `encodeBitsSymNative (n)`（元素位串，LSB 左）
- `encodeElementsSym (elems)`（α/β 头 + native，末元素 β 头）
- `filter_branch_encodeBitsSym/encodeElementsSym(_length)`、`encodeBitsSym_nonboundary`
- `joinLists`、`joinLists_map_sel_eq`、`encodeElementsSym_chosen_cell`、`encodeElementsSym_kind`
- `decodeBitsSym_encodeBitsSym`、`bitsOf/bitsValue_bitsOf/bitsOf_length`、`map_chosen_bits`
- `scanLeftKeepPos` 等格式检查引理

### 4.2 Mp/SubsetSumVerifierCore1.lean（已绿）
- 移入的 helper 块：`foldl` 系列、`21/16` 左扫、`format_sweep`、`step0` 系引理

### 4.3 Mp/SubsetSumVerifierCoreA.lean（已绿）
- `encodeElementsSymWithSel (elems) (sel)`（物理编码：每元素 `[sel/nosel] ++ native`）——**V1.0**
- `encodeElementsSymChosen (elems) (sel)`（逻辑选中编码：filterMap 只取选中元素 native）——**V1.0**
- `encodeElementsSymWithSel_eq_join`、`encodeElementsSymChosen_eq_join`、`encodeElementsSymChosen_length`
- `scanSelPrefix (elems) (tape) (p)`（从磁带逐块读回选择——NTM 内建语义）——**V1.0**
- `scanSelPrefix_length`、`encodeBitsSymNative_kind`、`WithSel_length`、`encodeElementsSym_cons_eq`、`WithSel_cons`、`encodeElementsSym_head_branch`、`encodeElementsSymWithSel_cell`
- `branch_phase`（签名含 `hne/hpos/htarget` + scan2 参数）
- `branch_phase_correct`（完备性：scan2 实例化为 `scanSelPrefix` 读回）
- `branch_with_sel`（给定 sel 版）
- `mem_zip_fst`（zip 第一分量投影的 mem）

### 4.4 Mp/SubsetSumVerifierCore2.lean（未绿，修复中）
- `main_loop_correct (elems) (sel) (tbits) (p_t) (p) (tape)`（状态 4→22 主循环；k 参数已移除）——**V1.0**
- `subAllSelected`、`targetTape`、`bitsValue/selectedSum` 等子集和数学层

### 4.5 Mp/SubsetSumVerifierReverse*.lean（未绿，上游依赖）
- Reverse/Reverse2：从接受路径读回 witness 的可靠性方向

### 4.6 Mp/SubsetSumVerifierCBTM*.lean（CBTM 层）
- `VerifierSym` 命名空间的 Sym 层转移表引理（CBTM4：`symTransition_nextState_mem`、`symTransition_write_not_branch_of_not_branch_read`、`symTransition_branch_row`、`transition_branch_not_q2_write`、`symTransition_write_mark_valid_br/nb`、`symTransition_write_sel_const/nosel_const` 等）
- CBTM.lean：`transition_card_two_of_branch`、`transition_nextState_le101`、`transition_write_notBranch`、`transition4_*`（F4 层）

### 4.7 数学层
- `Mp/IVM.lean`、`Mp/EssentialDimension.lean`、`Mp/PrimeSqrtLinearIndep.lean`、`Mp/LowerBound.lean`（SubsetSumInstance 定义）、`Mp/SubsetSumInNP.lean`、`Mp/FinalProof.lean`、`Mp/Barriers.lean`、`Mp/ClassicalFramework.lean`、`Mp/Basic.lean`

---

## 5. 对照表（概念模块 ↔ 证明概念 ↔ 具体模块）

| 概念性模块 | P vs NP 证明中的概念 | 具体模块（定义/引理/定理） |
|---|---|---|
| C1 编码 | 数计一体：语义内建在符号上（虚部 = 分支） | `Sym`、`encodeElementsSymWithSel`（物理，含 sel/nosel 选择符）、`encodeElementsSymChosen`（逻辑，仅选中位串） |
| C2 转移表 | 非确定转移：α/β 双分支 | `VerifierSym.transition` 的 `\| 2, (alpha,_) => {sel, nosel}` 行、`legalStates` |
| C3 路径 | 见证 = sel/nosel 序列；路径标记 Π∈{α,β}^m | `SymSteps`、`scanSelPrefix`（读回）、`encodeElementsSymWithSel_cell`（按实际写入逐格） |
| C4 分支阶段 | IVM 分叉：激活/不激活两路径 | `branch_phase`、`branch_phase_correct`、`branch_with_sel` |
| C5 主循环 | 子集和的逐元素相减（语义资源层） | `main_loop_correct`、`subAllSelected` |
| C6 逆方向 | 完备 witness 的读回 | `SubsetSumVerifierReverse*` |
| C7 主定理 | 维度 0 vs Ω(n) 矛盾 | `SubsetSumInNP`、`FinalProof` |
| C8 数学层 | 本质维度 κ、√p 独立性 | `EssentialDimension`、`PrimeSqrtLinearIndep`、`LowerBound` |

**见证对应（核心约定）**：CBTM = 路径标记 Π∈{α,β}^m；IVM = 激活向量 a∈{0,1}^m；语义展开 Φ : α↦1, β↦0 是双射。——**V1.0**

---

## 6. 具体事项约定（每条注明引入版本）

1. **可变长原生编码（k 全线移除）**：元素的位串 = `Nat.digits 2 v` 的可变长（LSB 左，不补零）；target 同理。旧 `maxBitWidth`/固定位宽 k 一律废弃。——**V1.0**
2. **target 不得为空**：若 target = 0 则编码为空，格式检查失败；证明中加前提 `htarget : 0 < inst.target`。——**V1.0**
3. **元素不得为 0**：加前提 `hpos : ∀ v ∈ inst.elements, 0 < v`（0 元素编码为空被格式检查拒绝）。——**V1.0**
4. **nosel 计入长度**：物理编码每块长度 = 1 标记 + native，与标记是 sel 还是 nosel 无关；长度对齐不许假设"全 sel"。——**V1.0**
5. **物理/逻辑编码分离**：`encodeElementsSymWithSel`（物理磁带，含选择符，供 tapeAgrees/scan2 校验）与 `encodeElementsSymChosen`（逻辑选中，仅 sel=true 的 native 拼接，供子集和数学验证）不得混用；长度与位置证明前先区分两类长度。——**V1.0**
6. **NTM 非确定语义**：α/β 格写 sel 或 nosel 是**真实双分支**（转移表 `{sel, nosel}` 两条），析取不可单值化；`if` 不能模拟非确定选择。——**V1.0**
7. **选择从磁带读回**：`scanSelPrefix` 从块头格的实际写入读回选择（写 sel = true，否则 false）；读回仅对格式合法磁带有意义（块头必为 sel/nosel）。——**V1.0**
8. **35 状态集合**：`legalStates` 手动列出 35 个合法状态（0,1,2,3,4,5,8,9,10,11,12,13,14,15,19,20,21,22,23,24,25,26,27,28,38,51,76,77,81,84,85,86,87,100,101），凡不在此集合的状态一律归 101 停机。——**V1.0**
9. **状态转移表一律不动**：转移表（`VerifierSym.transition` 的 match 臂）是既定规格，修改须用户明示。——**V1.0**
10. **转移表引理的证明模式**：对 transition 的证明用「显式 `if_pos/if_neg (by decide : q ∈ legalStates)` 一步归约 + native_decide 封闭枚举」，禁止裸 `simp [VerifierSym.transition]` 展开（会 isDefEq 超时/爆栈）。——**V1.0**
11. ~~**修复纪律**~~（**删除**——V1.5）
12. **语义优先**：顽固错误先分析本质原因（结构性根源：绕路旧编码/残留/依赖消去/归约前提），经用户澄清语义后再修；禁止症状级补丁。——**V1.0**
13. **版本命名**：论文/文档文件命名 `<主题>.<语言>.<大>.<小>`；修正递增小版本另存新文件。——**V1.0**
14. **编译方式**：单文件 `lake env lean Mp/<file>.lean`；全链 `lake build`；LF 换行；0 sorry；不编造证明。——**V1.0**
15. **文件归属与并行**：用户明令「不要修改 X 文件」或 sibling 并发改同一文件时，只列方案（根因 + 修法 + 风险表）等授权，不动手防冲突。——**V1.0**
16. **大型引理分离**：大引理移入独立文件，减少编译时间。——**V1.0**
17. **公理版路线**：在「子集和问题是 NP 完全问题」的公理下，**不需要构造具体 CBTM**；主链（FinalProof 的 P_F ≠ NP_F）以公理 + 已有定理组装先绿，验证器细节（Core1/Core2/Reverse）后续修复。——**V1.1**
18. **主公理形式**：`exists_NTM2_solves_subsetSum`——存在 NTM2 在 n（= 元素个数）次分叉后求解子集和（`subsetSumHolds inst ↔ ∃ 接受路径 ∧ ntm2ForkCount = elements.length`）；同构桥公理 `NTM2_solve_implies_IsNP_F`——NTM2 求解 ⇒ IsNP_F。——**V1.2**
18a. **公理登记（正式）**：`exists_NTM2_solves_subsetSum` 为**本项目的公理**，签名如下（登记于 Mp/SubsetSumInNP.lean）：
    `∃ A : NTM2, ∀ inst : SubsetSumInstance, inst.elements ≠ [] →
      (subsetSumHolds inst ↔ ∃ π, ReachablePathNTM2 A (encodeInstBits inst) π ∧
        NTM2ComputationPath.endState A π ∈ A.acceptStates ∧
        ntm2ForkCount A π = inst.elements.length)`
    语义：存在一台 NTM2，对每个非空实例，子集和成立当且仅当它有一条接受路径、且该路径的分叉次数恰为元素个数（每元素一次分叉）。该公理的消去目标：具体 NTM2 构造（SubsetSumNTM2 的翻译机器）的定理。——**V1.4**
19. **结构同构定理**：CBTM ≅ NTM2 的同构定理即 `StructIsoNTM2CBTM`（CBTM.lean:715）；`exists_CBTM_iso_NTM2`（CBTM.lean:787）已是定理（每个 NTM2 同构于某 CBTM）。桥公理的消去 = 该定理 + 待证的 `StructIso_preserves_accepts`（同构保持接受语言，由 h_transition 逐步对应归纳）。——**V1.3**

---

## 7. 版本记录

| 版本 | 日期 | 内容 |
|---|---|---|
| V1.0 | 2026-08-26 | 初版：目的、证明简介、概念模块、具体模块、对照表、16 条约定 |
| V1.1 | 2026-08-26 | 约定 17：公理版路线（不需构造具体 CBTM） |
| V1.2 | 2026-08-26 | 约定 18：主公理（NTM2 求解）+ 同构桥公理 |
| V1.3 | 2026-08-26 | 约定 19：结构同构定理 StructIsoNTM2CBTM 与公理消去路径 |
| V1.4 | 2026-08-26 | 约定 18a：exists_NTM2_solves_subsetSum 正式登记为本项目公理 |
| V1.5 | 2026-08-26 | 删除约定 11（修复纪律——每错 2 次上限不再约束） |

*（本文件为约定总纲；后续新约定按「约定 + 引入版本号」追加，并在本节登记。）*
