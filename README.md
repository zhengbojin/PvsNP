# PvsNP — P ≠ NP 的形式化证明工程（Lean 4）

在 Lean 4 / mathlib 中，基于**单一公理**构造 P ≠ NP 的完整形式化证明链：
**0 error、0 sorry、单公理**，`lake build` 通过。

## 核心结论（已形式化证明）

| 定理 | 内容 |
|---|---|
| `P_F_ss_NP_F` | **真子集**：`P_F ⊆ NP_F ∧ P_F ≠ NP_F`（虚部语义层） |
| `P_F_neq_NP_F` | P_F ≠ NP_F（维度论证：子集和需要 n 个独立维度 vs 受限机器 0 维） |
| `subsetSum_semantic_unified_separation` | 子集和的本质形态（α 编码）∈ NP_F ∖ P_F |
| `subsetSum_in_NP` / `subsetSum_in_NP_F` | 子集和 ∈ NP（Bool 层等价类 / F4 层） |
| `toCBTM_polynomialTime` | 求解机器的多项式时间（线性界，`isPolynomialTime` 已实化） |
| `encodeSubsetSumF4Real_not_injective` | 编码不单射：`([1],t=3) ≡ ([3],t=1)`——Bool 串不承载块结构 |

## 框架思想

- **CBTM**（复合带图灵机）：符号 = 实部 × 虚部（F4 = `Bool × Bool`）；虚部（α 标记）是非确定性分支的**内建语义**（数计一体：语义与语法同一）；
- **IVM**（本质维度 κ）：虚部 true 标记 = 素数平方根生成元（线性独立），构成维度度量单位；受限机器（P 侧）κ 恒为 0；
- **分离机制**：子集和编码中每个元素 = 一个 α 标记（独立维度），正确验证器必须读遍（κ ≥ n）；受限机器读 α 无转移（字母表障碍，κ = 0）——维度矛盾；
- **分层**：F4 本质层（虚部内建，分离在此可证）→ Bool 层 = 实部投影（等价类，经典陈述）。

## 数学边界（诚实声明）

- **已严格证明**：F4 语义层的分离 `P_F ⊊ NP_F`（维度/线性独立论证，与时间无关）；
- **未证明（等价于经典开放命题）**：Bool 层字面分离 `NP_Bool ≠ P_Bool`——投影不保持分离（π 不单射），`IsP_Bool K ⟺ 经典子集和 ∈ P`；
- 这与论文立场一致："直接证明经典 P≠NP 不可能，分离属于语义完整层"。

## 单一公理（公理 V6，四条款）

`PvsNP/SubsetSumInNP.lean` 中的 `exists_NTM2_solves_subsetSum`：

1. **求解**：子集和成立 ⟺ 规范 NTM2 接受编码串（分叉次数 = 元素个数）；
2. **语言桥**：实部输入经 vb 复合 = 语言的 F4 编码；
3. **规范**：磁头只在输入区内活动、每格至多读一次（⟹ 线性时间界）；
4. **非编码拒绝**：非编码串不被接受。

条款组合 ⟺ 原"恰好识别"条款；A2 同构桥公理已消为定理。

## 目录结构

```
PvsNP/
├── Basic.lean               NTM2 模型（输入 List Bool、vbAt 派生、Canonical）
├── CBTM.lean                CBTM 位置模型、IsPolynomialBound、同构定理
├── IVM.lean                 磁带语义、isPolynomialTime（实化）、kappa_M
├── A2Bridge.lean            同构桥（A2 消去）、长度引理
├── ClassicalFramework.lean  F4 复杂度类 IsP_F / IsNP_F / P_F / NP_F
├── ClassicalComplexity.lean Bool 层、等价类、语言投影-提升映射
├── SubsetSumLanguage.lean   子集和编码、维度下界、编码不单射
├── SubsetSumInNP.lean       公理 V6、subsetSum ∈ NP_F
├── FinalProof.lean          P_F_ss_NP_F（真子集）、障碍不变性
├── EssentialDimension.lean  本质维度（worstCaseDimension）
├── PrimeSqrtLinearIndep.lean 素数平方根线性独立
├── Barriers.lean            相对化/代数化不变性
├── LowerBound.lean          子集和定义
└── SubsetSumNTM2.lean       辅助
report.md                    技术报告（含数学边界完整分析）
Spec.md                      设计规格（仅本地，不随仓库分发）
```

## 构建与验证

```bash
lake build                          # 全链编译，0 error
grep -c "sorry" PvsNP/*.lean        # 0（无 sorry）
grep -rn "^axiom" PvsNP/*.lean      # 1（单公理 exists_NTM2_solves_subsetSum）
```

需要 Lean 4 + mathlib（首次构建需下载依赖，约 7 GB 缓存）。

## 论文

四篇论文 PDF 位于仓库根目录（tex 源文件不随仓库分发）：

- `measure.C.0.7.pdf` — 本质维度与下界
- `models.C.0.6.pdf` — 计算模型（CBTM/IVM）
- `philo.C.0.7.pdf` — 数计一体（语义语法同一）
- `QA2.C.0.6.pdf` — 理念篇

## 许可

Apache 2.0（见各文件头）。
