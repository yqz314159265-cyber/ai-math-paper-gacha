# 斐波那契素数是否有无穷多个？

> **100% AI 自动生成的数学论文抽卡实验（AI-Generated Math Gacha）**
>
> OpenAI Codex（GPT-6） · 2026-11-27 · **Partial**

设 $F_0=0, F_1=1, F_{n+2}=F_n+F_{n+1}$。本轮证明了任意固定的有限因子集都筛不掉充分大素数指标处的斐波那契数。但一个数可以避开全部小因子而仍为合数。实例如下：$F_{101}=743519377\times770857978613$，其最小非平凡因子大于 10,000。原猜想的无限性和它的否定均未证出。

## 原题与抽签

原题为 `FibonacciPrimes.fib_primes_infinite`，上游标签为 `category research open, AMS 11`。下列代码块给出完整声明头。项目把同一命题定义为 `MathGacha.Original`，所有部分结果均作为独立定理。复核脚本将本地命题逐词与原提交中的类型比较。[原题源码](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/FibonacciPrimes.lean#L28-L38) · [本地命题](Gacha/Statement.lean)

```lean
namespace FibonacciPrimes

theorem fib_primes_infinite : {n : ℕ | (∃ m : ℕ, m.fib = n) ∧ n.Prime}.Infinite
```

新建仓库的历史尝试数为零。按照“上游标为研究开放题，陈述仅用基本自然数函数并可做有限实验”的标准，先固定三个候选，再等概率抽取一次。

| 零起始索引 | 候选 | 研究对象 |
| ---: | --- | --- |
| 0 | [Erdős 287 的素数对变体](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/ErdosProblems/287.lean#L84-L95) | 二倍区间内的素数对 |
| 1 | [Erdős 1003](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/ErdosProblems/1003.lean#L33-L39) | 相邻整数的欧拉函数相等 |
| 2 | [FibonacciPrimes](Gacha/Statement.lean) | 斐波那契数列的素数值 |

随机源为 Python `secrets.token_bytes`。舍弃字节 255，其余 255 个值按模 3 均分。本轮首字节为 `d1`，即 $209\equiv2\pmod 3$。[抽签记录](draw.json) · [重放脚本](../../scripts/draw.py)

## 三条数学路线

**一、分解指标。** 若 $d\mid n$ 且 $3\le d<n$，则 $1<F_d<F_n$，且 $F_d\mid F_n$。当 $n>4$ 为偶数且选到的因子为 2 时，取互补因子 $n/2\ge3$。这给出 $F_n$ 为素数时 $n$ 为素数或 $n=4$，其中 $F_4=3$。反向推理在素数指标 19 处失效，因 $F_{19}=37\cdot113$。结合 $n\ge5$ 时 $F_n\ge n$，原题等价于在任意界限以上找到一个素数指标 $p$，使 $F_p$ 也为素数。[指标证明](Gacha/Index.lean) · [原题等价命题](Gacha/Reduction.lean)

**二、用互素性筛因子。** Mathlib 的 `Nat.fib_gcd` 给出 $\gcd(F_p,F_t)=F_{\gcd(p,t)}$。当 $p,t$ 是不同素数时，右边等于 1。于是一个给定的 $r>1$ 至多整除一个素数指标对应的项。对有限集合逐个加入因子，便得到一个界 $B$，使所有素数 $p>B$ 的 $F_p$ 都避开该集合。这也证明对任意 $K$，能找到均大于 $K$ 的素数 $p,q$ 使 $q\mid F_p$。要推得 $F_p$ 本身为素数，仍需排除同一项中的其他因子。[有限筛与大素因子的证明](Gacha/Sieve.lean)

**三、用平方和限制余数。** 倍角公式给出 $F_{2k+1}=F_{k+1}^2+F_k^2$，且相邻两项互素。Mathlib 关于互素平方和的定理给出 $-1$ 在模 $F_{2k+1}$ 下有平方根。由此证明，奇指标项的每个素因子要么等于 2，要么模 4 余 1。$F_{19}$ 的两个素因子 37、113 均模 4 余 1，说明这条同余限制容许一项同时具有多个因子。[平方和证明](Gacha/Squares.lean) · [Mathlib 平方和源码](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/SumTwoSquares.lean)

三条路线留下同一个量词问题。对每个**固定**筛界都能避开小因子，原题却要求对任意指标下界，选出一个 $p$ 并同时排除所有 $2\le d\le\lfloor\sqrt{F_p}\rfloor$ 的因子。这个随 $p$ 增长的筛界与原题的等价性也已形式化。下一步可研究这样的素数指标在区间内的计数下界，或者控制素数指标项出现两个以上素因子的频率。[等价性证明](Gacha/Reduction.lean)

Grantham 与 Granville 用线性递推数列的有限数据研究素数值分布，所给计数预测属于启发式。Bilu、Hanrot 与 Voutier 对 Lucas、Lehmer 数列证明了 $n>30$ 时原始素因子的存在性；这样的因子首次出现，命题仍允许它是该项的真因子。[Grantham–Granville 原文](https://arxiv.org/abs/2307.07894) · [Bilu–Hanrot–Voutier 原文及摘要](https://oskar-bordeaux.fr/handle/20.500.12278/165491)

## 计算结果与有限证明

| 范围 | 方法 | 结果 |
| --- | --- | --- |
| 所有 $0\le n\le93$ | Python 十二基确定性 Miller–Rabin；Lean 独立检查 | 素数值出现的位置恰为 **3、4、5、7、11、13、17、23、29、43、47、83** |
| 所有 $94\le p\le10000$ 的素数指标 | 枚举不超过 10,000 的素因子；用模递推独立复算 | 1,205 项中，102 项找到真因子，1,103 项通过该筛 |
| 通过筛的 $p=101$ | 显式分解，Lean 检查与 $10000!$ 的最大公因数 | $F_{101}$ 是合数，且没有 2 到 10,000 之间的因子 |

$F_{93}=12200160415121876738<2^{64}$，位于前十二个素数基的确定性范围内。Lean 对较大的素数值采用 Lucas 证书：$F_{43},F_{47},F_{83}$ 的模幂见证依次为 2、5、3；$F_{83}=99194853094755497$。这些整数的素性由内核检查因子分解和模幂等式。第二行的 102 对指标与因子逐对对应 Lean 的已验证列表。1,103 项中，除另行分解的 $F_{101}$ 外，本轮未逐项判定其素性。[Python 程序](experiment.py) · [完整数据](results.json) · [有限分类](Gacha/Certificates.lean) · [Lucas 证书](Gacha/Primality.lean) · [筛查证书](Gacha/Screen.lean) · [十二基界的来源](https://doi.org/10.1090/mcom/3134)

## Lean 验证

Lean 为 `v4.33.1`，Mathlib 提交为 `0df444a360eaa60ab8c11dca51a86af692955474`，与猜想池锁文件一致。全量 `lake exe cache get` 首次遇到 5 个传输失败，重试后 8,690 个缓存文件全部解压。对较大素数直接试除消耗过多内存，最终构建使用上述短证书。[依赖锁文件](../../lake-manifest.json) · [复现命令](../../README.md#复现本轮)

下列输出来自根目录的 `python scripts/audit.py`，包含 `lake build` 和逐个 `#print axioms`。原题作为命题定义保存。审计对象为本轮证明的定理和引理。

```text
lake build final line: Build completed successfully (3021 jobs).
Raw #print axioms output:
'MathGacha.fib_prime_indices_through_30' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_four_is_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_three_is_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_indices_through_93' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_excludes_proper_divisor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_index_prime_or_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.index_nineteen_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_nineteen_factorization' does not depend on any axioms
'MathGacha.fib_nineteen_not_prime' depends on axioms: [propext]
'MathGacha.primeMemProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasList' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.auxiliaryLucasPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeValue43' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeValue47' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeValue83' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffUnboundedPrimeIndices' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffSieveToSquareRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.screenWitnessesValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.screenTermsComposite' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.survivor101Composite' depends on axioms: [propext]
'MathGacha.survivor101NoSmallDivisor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_indices_coprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.finite_factors_avoid_fib_prime_indices' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.arbitrarilyLargePrimeFactors' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.minusOneSquareAtOddIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeFactorAtOddIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
Audit passed: lake build; 26 theorem/lemma axiom reports; 10 Lean files scanned.
```
