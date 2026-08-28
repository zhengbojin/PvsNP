# ParamEquiv.lean 编译错误修复技术报告

- 日期:2026-08-28
- 工程:D:\lean4\pvsnp(交付工程,单公理 A1 框架)
- 文件:PvsNP/ParamEquiv.lean
- 结论:`lake build` 全链通过,0 error、0 sorry

---

## 一、任务背景

参数化等价定理(论文 models.C.0.6.tex 定理 thm:equivalence 的语言层形态):
**CBTM|₀ ≡ₚₒₗy DTM**。PvsNP/ParamEquiv.lean 形式化其 P 方向外延等价
`P_cb0 = P_classic`(CBTM|₀ 判定的 Bool 语言类 = 经典 DTM 判定的 Bool 语言类)。

8 月 26 日构建遗留 **7 个编译错误**,本次全部修复,全链验证通过。

## 二、修复前状态

7 个错误分布:

| 位置 | 所属证明 | 错误类型 |
|---|---|---|
| 365:48 | cbtm0_path_to_dtm(CBTM0 路径 → toClassicDTM 路径重放) | unsolved goals |
| 686:4 | toCBTM_isCBTM0(位置无关条款) | unsolved goals |
| 706:8 | IsP_classic_subset_IsP_cb0(受限机器空白符号条款) | unsolved goals |
| 712:4 | IsP_classic_subset_IsP_cb0(投影接受反向) | unsolved goals |
| 728:33 | IsP_cb0_subset_IsP_classic(投影接受正向) | unsolved goals |
| 739:8 | IsP_cb0_subset_IsP_classic(受限机器虚部条款) | Type mismatch |
| 743:8 | IsP_cb0_subset_IsP_classic(受限机器空白符号条款) | Type mismatch |

## 三、根因分析

### 3.1 证明块缺失:cons 分支的最终格局等式(365:48)

cons 分支(refine 后)共 **5 个待证子目标**:
起始状态一致 → 读符号一致 → 转移一致 → 位置一致 → 最终格局一致。

原代码只有 **4 个证明块**,且第 4 块(`rw [hcfg']; dsimp [...]`)实际闭合的是
"位置一致"目标——该目标经重写与定义展开后自动归约为 rfl,被 dsimp 直接关闭。
结果:第 5 个目标(最终格局等式)没有任何证明块处理,成为未解目标;
同时第 4 块内后续行内 tactic 报"No goals to be solved"造成误导。

**修复**:补第 5 个证明块。最终格局等式用结构体单射定理 `DTMCfg.mk.injEq`
拆为三个字段(状态 / 磁带 / 带头位置):
- 状态、带头位置:两边的表达式定义上相同,rfl;
- 磁带:逐格展开(`funext i`),按"i 是否等于写位置"分两种情况,各分支 rfl。

### 3.2 simp 无法自动展开普通定义

四个错误同根因:simp 只展开 `@[simp]` 定理和显式列出的名字,
对普通 `def`(F4.re、boolToF4、Function.comp、F4.zero/F4.one)不做展开。

- **686:4(位置无关)**:`(D.toCBTM).transition (q, s, i) = ... (q, s, j)`。
  toCBTMTrans 的定义签名是 `fun (q, s, _i) => ...`,位置参数在模式中被丢弃,
  两边归约到同一表达式——应直接 `rfl`,而非 `simp`。
- **706:8(空白符号成员)**:`(D.toCBTM).blankSym ∈ (D.toCBTM).alphabet`。
  需要展开 `ClassicDTM.toCBTM` + `boolToF4` + `F4.zero`/`F4.one`
  才能归约到成员关系。补全 simp 参数列表。
- **712:4 / 728:33(嵌入串投影)**:`realProject (embedBool x) = x`。
  embedBool 与 realProject 都是 List.map 的复合,化简需要展开函数复合 `∘`
  与 `F4.re`,再逐点归约 `(b, false).1 = b`,最后应用 List.map_id。
  新增引理 `realProject_embedBool`(标 `@[simp]`):
  unfold 两定义 → `rw [List.map_map]` → 复合函数逐点 funext rfl 化简为恒等 → `rw [List.map_id]`。
  两处接受等价证明直接引用该引理。
- **739:8(虚部全 false)**:目标 `F4.im s = false`,前提 `s ∈ N.alphabet`。
  需:改写字母表等式 → simpa 把成员关系化简为析取 `s = zero ∨ s = one`
  → 分情况,各分支 rfl。原代码 `simpa using hs` 类型不匹配(成员关系 ≠ 等式)。

### 3.3 重写方向错误(743:8)

`h_blank_in_alphabet` 条款的目标本来就是 `N.blankSym ∈ N.alphabet`,
与 `N.h_blank_in_alphabet` 类型一致,直接 `exact` 即可。
原代码先 `rw [h0.alphabet_eq]` 把目标中的字母表替换为 `{zero, one}`,
导致引理类型(仍指向 N.alphabet)与目标错位。

### 3.4 ext / congr 陷阱(448:8)

- `ext` 对 DTMCfg **无适用的外延定理**(结构体未自动注册,探针验证报
  "No applicable extensionality theorem");
- `congr` 在已闭合的目标上报"No goals to be solved",被误读为证明已完成;
- 正确路径:结构体单射定理 `DTMCfg.mk.injEq`(探针验证后采用)。

## 四、验证结果

```
lake build PvsNP.ParamEquiv   → EXIT 0,0 error
lake build(全链)             → EXIT 0,0 error
grep sorry / admit            → 无
git status                    → 仅 PvsNP/ParamEquiv.lean 修改
```

说明:全链构建中出现两轮 `.olean.private` 瞬时读取失败
(Windows 并行编译的 I/O 竞争,错误文件每次不同),重试即恢复——非代码问题,
与上次会话观测一致。

## 五、技术要点(可复用经验)

1. **结构体等式分解**:优先 `X.mk.injEq`,`ext` 未必可用、`congr` 在 rfl 目标上
   报 No goals 会误导诊断。
2. **"No goals to be solved" 的信号**:某证明块内的行内 tactic 报此错,
   通常意味着该块处理的目标已被前面的 rw/dsimp 闭合——此时应检查
   refine 产生的目标总数与证明块数量是否一致(本项目即少一个证明块)。
3. **simp 不展开普通 def**:F4.re、boolToF4、Function.comp 等需显式列出,
   或提炼为 `@[simp]` 引理(realProject_embedBool 模式)。
4. **rfl 目标的闭合**:dsimp 会把归约到 rfl 的目标直接关闭,其后无需(也不能)
   再放 rfl。
5. **瞬时 .olean.private 读取失败**:Windows 并行编译 I/O 竞争,重试即恢复。
