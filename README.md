# Ramanujan τ 素数值：平方层与四次层的条件性 Lean 证明

本项目整理了两个经 Lean 4 内核检查的**条件性定理**：在正整数形式的 $abc$ 猜想及相应素数幂 Hecke 恒等式下，控制整数序列在平方层和四次层所取的不同素数绝对值。形式化中的这些前提是定理的参数，而不是从序列的有限乘积定义推导出的结论。

## 定理及精确前提

设 $t:\mathbb N\to\mathbb Z$，定义

$$S_k(X;t)=\#\{\ell\le X:\ell\text{ 为素数，存在素数 }p,\ |t(p^{2k})|=\ell\}.$$

* `TauSquareLayer.square_layer_bound`：对每个素数 $p$ 假设 $t(p^2)=t(p)^2-p^{11}$，再假设 `TauTarget.abcConjecture`，则对每个 $\varepsilon>0$，$S_1(X;t)\ll_\varepsilon X^{2/9+\varepsilon}$。
* `TauFourthLayer.layer_bound`：对每个素数 $p$ 假设 $t(p^4)=t(p)^4-3p^{11}t(p)^2+p^{22}$，再假设 `TauTarget.abcConjecture`，则对每个 $\varepsilon>0$，$S_2(X;t)\ll_\varepsilon X^{1/10+\varepsilon}$。证明显式处理 $p=2$ 和素数值 $\ell=5$。

以上 $O$ 表述在 Lean 中具体为：任意 $\varepsilon>0$，存在 $C>0$ 和整数 $N$，对所有自然数 $X\ge N$ 成立相应不等式。常数可能依赖 $\varepsilon$ 和 $abc$ 假设。`TauAssembly.layer` 直接以不同素数值的有限集合定义计数。

**重要限制：** 此项目没有证明有限 $q$ 乘积系数 `tauTruncated` 与解析模判别式 $\Delta$ 的 Fourier 系数相同，也没有从该定义证明真实 $\tau$ 的 Hecke 恒等式、乘法性或其他算术性质。项目没有证明高次层上界，也没有从 $abc$ 猜想单独推出整个素数值计数的 $2/9+\varepsilon$ 上界。`TauTarget.conditionalGoal` 只是命题定义，不是已证明定理。要将这里的层定理用于真实 $\tau$ 函数，仍须独立接入或形式化其 Hecke 恒等式。

## 编译

环境为 Lean `v4.32.2` 与 Mathlib `v4.32.2`，`lake-manifest.json` 固定依赖提交。安装 [elan](https://github.com/leanprover/elan) 后，在仓库根目录运行：

```sh
lake exe cache get
lake build
```

如需查看两条最终定理的完整类型及公理依赖，可在本目录创建或打开 Lean 文件：

```lean
import TauSquareLayer
import TauFourthLayer

#check TauSquareLayer.square_layer_bound
#check TauFourthLayer.layer_bound
#print axioms TauSquareLayer.square_layer_bound
#print axioms TauFourthLayer.layer_bound
```

`#print axioms` 所列基础项与定理中的参数是两个不同概念：即使输出中没有 `sorryAx`，上述 $abc$ 和 Hecke 恒等式仍然是显式前提。

## 项目结构

`TauAssembly.lean` 和 `TauLayerBridge.lean` 处理去重计数；`TauArithmetic.lean`、`TauCoprime.lean`、`TauRadical.lean` 与 `TauSignedAbc.lean` 给出算术及 $abc$ 辅助步骤。`TauSquare*.lean`、`TauFourth*.lean` 分别构成两条证明；其他包含的 `Tau*.lean` 文件是它们的依赖。
