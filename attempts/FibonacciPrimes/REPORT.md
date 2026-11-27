# 斐波那契素数是否有无穷多个？

> **100% AI 自动生成的数学论文抽卡实验（AI-Generated Math Gacha）**
>
> OpenAI Codex（GPT-6） · 2026-11-27 · **Partial**

设 $F_0=0, F_1=1, F_{n+2}=F_n+F_{n+1}$。本轮证明，对任意固定的倍数 $K$，存在任意大的素数指标 $p$，使 $F_p$ 的最小素因子大于 $Kp$。但一个数可以避开全部小因子而仍为合数。实例如下：$F_{101}=743519377\times770857978613$，其最小非平凡因子大于 10,000。原猜想的无限性和它的否定均未证出。

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

随后将 Lean 的完整分类延长至 $n=137$。在 $94\le n\le137$ 中，恰有两项为素数：

| 指标 $n$ | $F_n$ | Lucas 模幂见证 |
| ---: | ---: | ---: |
| 131 | 1,066,340,417,491,710,595,814,572,169 | 3 |
| 137 | 19,134,702,400,093,278,081,449,423,917 | 2 |

对这两项，Python 用试除法完整分解 $F_n-1$ 并找到见证。Lean 独立核验分解中每个素因子的素性、乘积和全部模幂条件。对同一区间中的其余素数指标，取七个已知因子的乘积，逐项核实它与 $F_n$ 的最大公因数严格介于 1 和 $F_n$ 之间。故前 138 项（从 $F_0$ 起）恰有 14 个素数项。[完整分类与证书](Gacha/LargePrefix.lean) · [Python 复算](lucas_certificates.py)

## 随素数指标增长的筛界

令 $P^-(t)$ 表示 $t>1$ 的最小素因子。本轮进一步证明

$
\forall K,B\in\mathbb N,\quad \exists\text{ 素数 }p>B,\qquad P^-(F_p)>Kp.
$

因此，即使把筛界从一个常数提高为指标的任意固定倍数，也总有任意远的素数指标通过筛查。[Lean 定理及其构造](Gacha/LinearSieve.lean)

**第一步是限制因子的剩余类。** 设 $p>5$ 为素数，$q$ 为 $F_p$ 的素因子。由 $\gcd(F_m,F_n)=F_{\gcd(m,n)}$ 可知，凡 $q\mid F_t$，必有 $p\mid t$。对 $q\ne2,5$，在特征 $q$ 的代数闭包中取 $X^2-X-1$ 的两根 $a,b$。两根不同，且 $(a-b)F_n=a^n-b^n$。Frobenius 映射 $x\mapsto x^q$ 固定或交换这两个根，分别给出 $q\mid F_{q-1}$ 或 $q\mid F_{q+1}$。因子 2 和 5 已分别出现在 $F_3$ 和 $F_5$，因此不会出现在此处的 $F_p$。综上，$q=kp+1$ 或 $q=kp-1$，奇偶性又给出 $q\ge2p-1$。当 5 在模 $q$ 下有平方根时，可以直接选择 $q-1$ 这一支。这是经典出现秩关系的 Lean 证明。[Frobenius 证明](Gacha/Frobenius.lean) · [指标整除](Gacha/FactorRank.lean) · [分裂情形](Gacha/SplitPrime.lean) · [Ward，1961，第 2 节](https://msp.org/pjm/1961/11-1/pjm-v11-n1-p31-s.pdf)

**第二步是同时使小倍数对应的线性式成为合数。** 固定 $K$，取 $M_K=\prod_{1\le k\le K}(3k-1)(3k+1)$。因为 $3$ 与 $M_K$ 互素，狄利克雷定理保证模 $M_K$ 余 3 的素数 $p$ 任意大。取 $p>5$。对每个 $1\le k\le K$，数 $kp-1$ 有真因子 $3k-1$，而 $kp+1$ 有真因子 $3k+1$。第一步已经覆盖 $q\le Kp$ 的所有可能情形，故整条剩余类中的这些素数指标都满足 $P^-(F_p)>Kp$。[线性式的真因子与狄利克雷证明](Gacha/LinearSieve.lean)

固定 $K$，对所有满足 $P^-(F_p)>Kp$ 的素数指标 $p$ 求和，得到 $\sum_p (\log p)/p=\infty$。证明利用同一剩余类中素数的加权级数发散，再逐项比较。这个结论给出了通过筛查的指标集合的一种定量大小。[加权级数的 Lean 证明](Gacha/WeightedSieve.lean)

**筛界距离素性检验还有多远。** Lean 证明 $8^K\le M_K$。对上述剩余类中的 $p\ge50$，有 $M_K\mid p-3$，于是 $K<p$。另用二步归纳证明了 $F_p\ge p^4$，合起来得到 $Kp<p^2\le\lfloor\sqrt{F_p}\rfloor$。这个不等式限定了本构造实际保证的排除范围。要证明原题，还须控制同一个 $F_p$ 在其余区间内的素因子。[已验证的构造界](Gacha/Cutoff.lean)

还用独立的有限状态方法证明了，对每个整数 $m>1$，存在 $1\le t\le m^2$ 使 $m\mid F_t$。证明在模 $m$ 的 $m^2$ 对状态 $(F_n,F_{n+1})$ 中找出碰撞，再用转移 $(a,b)\mapsto(b,a+b)$ 的单射性退回初态。由此，给定任意有限因子集 $S$，对素数指标 $p>\max_{r\in S}r^2$，其中每个 $r>1$ 都不整除 $F_p$。[有限状态证明](Gacha/Period.lean)

**数值边界。** Python 在 $5<p\le250000$ 的素数中依次检查所有 $kp\pm1$。表中 $p$ 是使两组线性式对每个 $1\le k\le K$ 均为合数的最小素数指标。这项条件足以通过筛查；若某个线性式为素数，仍需检验它是否整除 $F_p$。

| $K$ | 1 | 2 | 4 | 8 | 16 | 32 | 64 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 首个符合条件的 $p>5$ | 7 | 13 | 47 | 167 | 881 | 17,209 | 246,809 |

对其中两个合数项，Lean 核实了**最小**素因子的精确值：$P^-(F_{881})=264301=300\cdot881+1$；$P^-(F_{17209})=5197117=302\cdot17209-1$。证明先核实整除，再用两条允许的剩余类排除全部较小素因子。Python 使用模快速倍增独立复算。[实验程序](linear_experiment.py) · [实验数据](linear_results.json) · [Lean 最小因子证书](Gacha/MovingScreen.lean)

Grantham 与 Granville 在第 3.3 节对指标上界 $N$ 给出的启发式预测为 $e^\gamma\log_\varphi N$ 个素数项，其中 $\varphi=(1+\sqrt5)/2$。上面的剩余类结论控制小素因子，而这个预测涉及整项的素性，仍需新的计数论证。[原论文第 3.3 节](https://arxiv.org/html/2307.07894#S3.SS3)

## 整项素性的计数判据

令 $\Lambda$ 为冯·曼戈尔特函数。对每个 $n>1$，若 $n$ 为素数，则 $\Lambda(n)=\log n$。若 $n$ 为合数，其最小素因子 $r$ 满足 $r^2\le n$，而 $\Lambda(n)$ 取 $0$ 或 $\log r$，所以 $2\Lambda(n)\le\log n$。这个阈值给出了一个可用于计数的权重

$$
w(n)=\frac{\max(2\Lambda(n)-\log n,0)}{\log n}.
$$

在所有 $n>1$ 上，素数贡献 1，合数贡献 0，包括素数的高次幂。由此无条件得到原题的充要条件：在所有素数指标 $p>5$ 上，级数 $\sum_p w(F_p)$ 发散。这里每一项只数整个 $F_p$ 的素性。前一节已证发散的级数则会把通过小因子筛查的合数也算进去。两者之间尚缺一个对真正素数项数目的下界。[阈值与级数的 Lean 等价证明](Gacha/WholeTerm.lean)

Bugeaud、Mignotte 和 Siksek 已证明斐波那契数中的完全幂只有 $0,1,8,144$。由他们的结果，素数指标 $p>5$ 的合数项甚至不能是素数幂。上面的阈值证明对所有自然数都适用，Lean 编译不依赖这项外部定理。[原论文](https://annals.math.princeton.edu/2006/163-3/p05)

还可以逐个追踪重因子。若 $p>5$ 与 $q$ 都为素数且 $q^2\mid F_p$，已证的指标同余给出 $p\mid q-1$ 或 $p\mid q+1$。于是 $F_p$ 整除对应的邻项，故 $q^2\mid F_{q-1}$ 或 $q^2\mid F_{q+1}$。反过来说，若对每个素数 $q$ 均能排除两个邻项中的平方因子，那么每个这样的 $F_p$ 都无平方因子。这个条件结论仍允许 $F_p$ 为两个不同素数的乘积。[重因子的 Lean 证明](Gacha/RepeatedFactor.lean)

## 最小素因子什么时候达到下界？

对每个素数 $p>5$，令 $q=2p-1$。我们证明了精确判据

$$
P^-(F_p)=2p-1
\quad\Longleftrightarrow\quad
q\text{ 是素数，且 }p\bmod5\in\{2,4\}.
$$

在这个位置，$q\mid F_p$ 与 $P^-(F_p)=q$ 等价。若 $q$ 是合数且整除 $F_p$，则 $q$ 自身的最小素因子也整除 $F_p$，却小于已证的下界 $2p-1$。当 $q$ 为素数时，在模 $q$ 的代数闭包中取特征根 $a,b$。由 $ab=-1$、$p$ 为奇数、$2p=q+1$，将 $(a^p-b^p)^2$ 展开，并代入 $a^q+b^q=1$，得到 $2F_p^2\equiv1+F_q\pmod q$。而 $F_q\bmod q$ 等于勒让德符号 $(5/q)$。二次互反律把该符号的负值化为 $q\bmod5\in\{2,3\}$，也就得到了上式。若 $p>7$，还有 $2p-1<F_p$，于是整项必为合数。Drobot 在 2000 年证明了这条合数充分条件；这里另行验证了逆向与最小因子等价式。$p=7$ 解释了两个结论边界的区别：$2p-1=F_7=13$。[Drobot 原文](https://www.mathstat.dal.ca/FQ/Scanned/38-1/drobot.pdf) · [模素数的符号](Gacha/IndexResidue.lean) · [边界判据](Gacha/Drobot.lean)

若 $2p-1$ 没有整除 $F_p$，则其最小素因子至少为 $4p+1$。原因是每个素因子 $q$ 除了满足 $q=kp\pm1$，还满足 $q\equiv1\pmod4$。枚举 $1\le k\le4$，严格小于 $4p+1$ 的数中只剩 $2p-1$ 这一种可能。两个端点都能达到：$F_{19}$ 的最小素因子是 $37=2\cdot19-1$，$F_{67}$ 的最小素因子是 $269=4\cdot67+1$。[间隔及端点证明](Gacha/Drobot.lean)

在 $7<p\le10^6$ 的 78,494 个素数指标上，Python 用快速倍增直接计算 $F_p\bmod(2p-1)$，并独立筛出 $2p-1$ 的素性。7,749 个指标令 $2p-1$ 为素数，其中恰有 5,175 个使其整除 $F_p$。这 5,175 个因子均只出现一次。各余数类的计数和前十二个实例见实验数据。要从这个合数判据导出无限族，还需要满足指定余数条件的素数对 $(p,2p-1)$ 无穷多。[实验程序](boundary_experiment.py) · [计数结果](boundary_results.json)

符号还可以指定一个因子出现在哪个剩余类里。若 $(5/p)=-1$，那么 $F_p$ 至少有一个素因子 $q\equiv-1\pmod p$：否则其全部素因子模 $p$ 都等于 1，乘积便与 $F_p\bmod p$ 矛盾。对前述任意 $K$ 的构造，把模数改为 $5M_K$，仍取余 3，就能额外保证这个负号。因此任给 $K,B$，存在素数 $p>B$ 与 $q>Kp$，使 $q\mid F_p$ 且 $p\mid q+1$。[带指定剩余类的大因子](Gacha/SignedSieve.lean)

## 因子重数与筛后候选

若 $p\ge1$，$F_p$ 整除 $F_{kp}$。通过对 $k$ 同时归纳 $F_{kp}$ 与 $F_{kp+1}$ 的同余，我们得到整数商的精确公式

$$
\gcd(F_{kp}/F_p,F_p)=\gcd(k,F_p).
$$

于是只要素数 $q\mid F_p$ 且 $q\nmid k$，取任意 $e\ge1$，便有 $q^e\mid F_{kp}\iff q^e\mid F_p$。用于素数指标 $p>5$，得到 $q^e\mid F_p$ 当且仅当 $q^e$ 整除 $F_{q-1}$ 或 $F_{q+1}$。反向的理由是，凡 $q\mid F_{q\pm1}$ 都有 $p\mid q\pm1$，而 $q$ 不整除该指标乘数。这把上节关于平方因子的单向判断加强到所有重数。关于斐波那契数的素因子赋值，Lengyel 给出了更一般的结果。[整数商与重数证明](Gacha/FactorLift.lean) · [Lengyel 原文](https://www.fq.math.ca/Scanned/33-3/lengyel.pdf)

Fengsui Liu 在 2020 年论文的定理 4.2 中尝试用有限候选集的增长证明原猜想。证明 A 从两个集合序列有相同极限推断其基数极限相同；证明 B 计算一个终端区间在基数映射下的原像时，把未知极限集合计入了原像。这一步需要先证明它的基数超过每个有限界。可以用一个非空极限检验该推理：取 $A=\{0\}$，$T_n=\{0\}\cup[n+1,2n+1]$，$L_n=\{0\}\cup\{x>n\}$。有 $A\subseteq T_n\subseteq L_n$，每个固定整数是否属于 $T_n$ 最终都与 $A$ 一致，但 $|T_n|=n+2$ 而 $|A|=1$。这个例子针对基数极限的推理，原猜想保持开放。[Liu 原文，第 IV 节](https://globaljournals.org/GJSFR_Volume20/1-There-are-Infinitely-Many-Fibonacci-Primes.pdf) · [逐点极限与基数反例](Gacha/SieveLimit.lean)

对实际斐波那契筛，Lean 证明了能排除这种情形的充要条件。给定任何下界 $B$，须先找到一个固定上界 $N$；再对每一筛界 $K$，都能在 $B<p\le N$ 找到一个素数指标，使 $F_p$ 没有不超过 $K$ 的**真**素因子。因为现在可以取 $K=F_N$，所得的足够大指标对应整项必为素数。反向直接用一项已为素数的 $F_p$ 并令 $N=p$。已有狄利克雷构造中的指标随 $K$ 改变，它能否被限制在这样的固定区间内，正是需要的新估计。[固定区间判据](Gacha/SieveLimit.lean)

## Lean 验证

Lean 为 `v4.33.1`，Mathlib 提交为 `0df444a360eaa60ab8c11dca51a86af692955474`，与猜想池锁文件一致。全量 `lake exe cache get` 首次遇到 5 个传输失败，重试后 8,690 个缓存文件全部解压。对较大素数直接试除消耗过多内存，最终构建使用上述短证书。[依赖锁文件](../../lake-manifest.json) · [复现命令](../../README.md#复现本轮)

下列输出来自根目录的 `python scripts/audit.py`，包含 `lake build` 和逐个 `#print axioms`。原题作为命题定义保存。审计对象为本轮证明的定理和引理。

```text
lake build final line: Build completed successfully (3860 jobs).
Raw #print axioms output:
'MathGacha.fib_prime_indices_through_30' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_four_is_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_three_is_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_indices_through_93' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.modulusExponentialLowerBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fourthPowerBelowFib' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.dirichletCutoffBelowSquareRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibHalfNeighborSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.boundaryDvdIffNegative' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeOfBoundaryDvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibAboveBoundary' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.boundaryDvdIff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactorAtBoundaryIff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.compositeAtBoundary' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeFactorGap' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactorGap' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactor67' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibMulFirstOrder' depends on axioms: [propext, Quot.sound]
'MathGacha.fibQuotientGcd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimePowerAtMultiple' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimePowerAtNeighbors' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.indexDividesFromCommonFactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimeFactorCongruence' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibLeastFactorLinearBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.divisorProgressionUpTo' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.noSmallFactorFromCompositeForms' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPowerDifference' depends on axioms: [propext, Quot.sound]
'MathGacha.fibRootsFromDiscriminant' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibRootsAtPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibFrobeniusZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_excludes_proper_divisor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_index_prime_or_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.index_nineteen_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_nineteen_factorization' does not depend on any axioms
'MathGacha.fib_nineteen_not_prime' depends on axioms: [propext]
'MathGacha.fib_prime_index_eq_pow_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_index_eq_legendre' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_index_eq_one_or_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.exists_prime_factor_eq_neg_one_mod' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.legendreSym_five_eq_neg_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.factors_131_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_131_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_131_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.factors_137_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_137_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_137_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sieve_gcd_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_index_excluded_by_sieve' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.old_index_le_93' depends on axioms: [propext, Quot.sound]
'MathGacha.fib_prime_indices_through_137' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.linearFormsModulusCoprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.compositeLinearFormsOnClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.arbitrarilyLargePrimeWithCompositeLinearForms' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactorBoundOnClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.unboundedLeastFactorOverIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactorCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactor881' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactor17209' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibState_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibState_succ' depends on axioms: [propext, Quot.sound]
'MathGacha.fibState_step_injective' depends on axioms: [propext, Quot.sound]
'MathGacha.fibState_collision_returns' depends on axioms: [propext, Quot.sound]
'MathGacha.exists_fib_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.no_fib_factor_at_prime_above_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.finite_factors_avoid_square_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeMemProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasList' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.auxiliaryLucasPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeValue43' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeValue47' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeValue83' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffUnboundedPrimeIndices' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffSieveToSquareRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeSquareFibFactorAtNeighbor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibAtPrimeSquarefreeOfNoNeighborSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.screenWitnessesValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.screenTermsComposite' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.survivor101Composite' depends on axioms: [propext]
'MathGacha.survivor101NoSmallDivisor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_indices_coprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.finite_factors_avoid_fib_prime_indices' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.arbitrarilyLargePrimeFactors' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.candidateA_subset_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.candidateT_subset_L' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.candidateT_eventually_eq_A_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.candidateT_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffUniformFiniteSieve' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.negativeLargeFactorForEveryTail' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_q_sub_one_dvd_of_five_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.splitPrimeFactorDividesQSubOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.minusOneSquareAtOddIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeFactorAtOddIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.not_summable_largeLeastFactorWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.wholeTermPrimeThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffUnboundedMangoldtThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeMass_eq_indicator' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffNotSummableFibPrimeMass' depends on axioms: [propext, Classical.choice, Quot.sound]
Audit passed: lake build; 97 theorem/lemma axiom reports; 26 Lean files scanned.
```
