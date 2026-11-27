# 斐波那契素数是否有无穷多个？

> **100% AI 自动生成的数学论文抽卡实验（AI-Generated Math Gacha）**
>
> OpenAI Codex（GPT-6） · 2026-11-27 · **Partial**

设 $F_0=0, F_1=1, F_{n+2}=F_n+F_{n+1}$。本轮证明存在任意大的素数指标 $p$，使 $F_p$ 的最小素因子超过 $2^{-30}p\log p$，其中 $\log$ 是自然对数。证明给出显式的素数对计数上界。此前用不同的构造还证明了对任意 $A>1/2$ 的下界 $p\log\log(p)/A$。排除小因子之后，整项仍有可能是合数。实例如下：$F_{101}=743519377\times770857978613$，其最小非平凡因子大于 10,000。原猜想的无限性和它的否定均未证出。

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

## 用有限域多项式判定全部候选因子

设 $q>5$ 为素数，$\chi_q=(5/q)$ 是勒让德符号，$t=q-\chi_q$。当 $q\bmod5$ 为 2 或 3 时取 $t=q+1$，其余情况取 $q-1$。记 $D_0=2,\ D_1=X,\ D_{k+2}=X D_{k+1}-D_k$。对任意素数指标 $p$，本轮证明了

$$
q\mid F_p\quad\Longleftrightarrow\quad
p\mid t\quad\text{且存在 }z\in\mathbb F_q\text{ 使 }D_{t/p}(z)=-3.
$$

证明用到两个信息。首先，在模 $q$ 下有 $2F_{q-1}=1-\chi_q$ 和 $2F_{q+1}=1+\chi_q$，故 $q\mid F_t$。若 $q$ 也整除 $F_p$，斐波那契数的最大公因数公式给出 $p\mid t$。其次，在 $\mathbb F_q$ 的代数闭包中取 $X^2-X-1$ 的两根 $a,b$ 并令 $r=a/b$。则 $r+r^{-1}=-3$、$r\ne r^{-1}$，且 $q\mid F_n$ 恰好当 $r^n=1$。[相邻指标公式](Gacha/SharpRank.lean) · [根的比值与幂](Gacha/DicksonFactors.lean)

写 $t=kp$。若 $r^p=1$，取 $u^k=r$，则 $u^t=1$。由于 $t=q\pm1$，Frobenius 将 $u$ 送到 $u$ 或 $u^{-1}$，所以 $z=u+u^{-1}$ 落回底域，且 $D_k(z)=u^k+u^{-k}=-3$。反过来，把底域中的解写成 $u+u^{-1}$。因为两个非零元素有相同的逆元和当且仅当它们相等或互逆，可以在 $u,u^{-1}$ 中选出一个使 $u^k=r$。又因 $r\ne r^{-1}$，Frobenius 对 $u$ 必须采用与 $r$ 相同的作用，故 $u^t=1$，从而 $r^p=1$。[有限域下降和逆元和](Gacha/TraceRoots.lean) · [双向证明](Gacha/DicksonFactors.lean)

由此得到一个右侧完全不含斐波那契数的原题等价式。对每个 $B$，须存在素数 $p>\max(B,5)$，使每个满足 $5<q\le 2^{\lfloor p/2\rfloor}$ 和 $p\mid q-\chi_q$ 的素数 $q$ 都有 $D_{(q-\chi_q)/p}(z)\ne-3$ 对所有 $z\in\mathbb F_q$ 成立。筛界之所以够用，是因为对这些指标有 $\lfloor\sqrt{F_p}\rfloor\le 2^{\lfloor p/2\rfloor}<F_p$。给定 $p$ 时由此可以判定素性。无限性还要求在任意下界之上，找到同时通过整个筛界的同一个 $p$。[原题等价式](Gacha/DicksonSieve.lean)

对 $7\le q\le5000$ 的全部素数，遍历 $q-\chi_q$ 的每个素因子 $p>5$。一条计算路径在 $\mathbb F_q$ 穷举 $z$，另一条用倍增公式算 $F_p\bmod q$。分裂分支 357 对中有 13 对整除，非分裂分支 428 对中有 61 对整除。785 对的判断全部一致。例如 $p=37,q=149$ 时 $k=4$，底域中的解恰为 $16,33,116,133$。[计算程序](dickson_experiment.py) · [逐分支数据](dickson_results.json)

多项式检验也可以只用除法。$X^q-X$ 的根恰是 $\mathbb F_q$ 全体元素，因此逐点排除根等价于 $D_k+3$ 与 $X^q-X$ 互素。每个实际素因子的乘数 $k$ 还必须落在以下两个分支之一。

| 因子 | $k\bmod4$ | $kp\bmod5$ |
| --- | ---: | --- |
| $q=kp+1$ | 0 | 0 或 3 |
| $q=kp-1$ | 2 | 3 或 4 |

特别地，所有 $k\equiv10\pmod{20}$ 均可排除。用多项式取余和欧几里得算法检查 $q\le100000$、$k\in\{2,4,6,8,10,12\}$ 的 2,208 对候选，其中 664 对的最大公因式次数为 $k$，其余 1,544 对次数为 0。$k=10$ 的 207 对全部互素，与上表一致。[互素判据与乘数限制](Gacha/DicksonTests.lean) · [多项式算法](polynomial_gcd_experiment.py) · [分次数统计](polynomial_gcd_results.json)

在第二个可能的因子位置 $q=4p+1$，我们还检查了 $7\le p\le10^6$ 的全部 78,495 个素数指标，共有 1,255 个满足 $q\mid F_p$。在 $q$ 为素数且 $p\equiv2\pmod5$ 的 2,525 个实例中，逐项独立检验了 $q=x^2+100y^2$，与整除性全部一致。该二次型刻画来自 Emma Lehmer（1966）定理 2 在 $q\equiv29\pmod{40}$ 分支的结论。下文给出适用于全部素数指标 $p>5$ 的 Lean 证明，并把二次型改写为指标 $p$ 本身的表示。[Lehmer 原文，第 137 页](https://www.fq.math.ca/Scanned/4-2/lehmer.pdf) · [第二位置实验](four_experiment.py) · [结果](four_experiment_results.json)

## 固定线性筛界的 Abel 权重

令 $S_K$ 为满足 $P^-(F_p)>Kp$ 的素数指标集合。我们已证明，对每个固定的 $K$ 和每个 $c<1/\varphi(M_K)$，当实数 $s>1$ 充分接近 1 时，

$$
(s-1)\sum_{p\in S_K}\frac{\log p}{p^s}>c.
$$

这里 $M_K$ 是前面构造的模数。证明计算一个可逆剩余类的素数 Abel 权重，分离高次素数幂，再扣除指标小于 6 的有限修正。这个结论给出了固定 $K$ 下筛后集合的定量下界；当筛界随 $p$ 增至检验整项素性所需的范围时，仍缺少相应估计。[Abel 权重证明](Gacha/AbelSieve.lean)

## 最小素因子的显式超线性下界

记 $P^-(F_p)$ 为 $F_p$ 的最小素因子，$\log$ 为自然对数。对每个 $B$，存在素数 $p>B$ 满足

$$
P^-(F_p)>\frac{p\log\log p}{20}.
$$

为此令 $K=\max(B,5)$，$M=\operatorname{lcm}(1,\ldots,K+1)$，取 $p$ 为整数 $\lvert\Phi_M(M)\rvert$ 的最小素因子。这个数大于 1。$M$ 在模 $p$ 乘法群中的阶恰为 $M$，故 $M\mid p-1$。由 $\Phi_M(M)\mid M^M-1$ 得到 $M<p\le M^M$。这个上界使我们可以用实际选出的 $p$ 表示筛界。[圆分多项式与显式素数界](Gacha/EffectiveSieve.lean)

若 $q\le Kp$ 是 $F_p$ 的素因子，则 $q=jp\pm1$，其中 $1\le j\le K$。因为 $p\equiv1\pmod5$，前述因子间隔已排除 $j\le2$。当 $j\ge3$ 时，$j+1$ 和 $j-1$ 均整除 $M$；由 $p\equiv1\pmod M$，$jp+1$ 和 $jp-1$ 分别有真因子 $j+1$ 和 $j-1$。这排除了全部候选。再由切比雪夫估计 $\log M=\psi(K+1)\le7(K+1)$ 和 $p\le M^M$，化得 $\log\log p\le20K$，于是得到所述不等式。[余 1 筛与增长定理](Gacha/EffectiveSieve.lean) · [Mathlib 切比雪夫估计](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean)

对 $K=4,\ldots,35$，Python 逐个找到模 $M$ 余 1 的最小素数，并用模倍增检查筛界内的每个线性候选。$K=35$ 时，$M=144403552893600$，$p=1010824870255201$。Lean 以底数 43 和 $p-1$ 的完整分解验证了指标 $p$ 的素性，再证明 $P^-(F_p)>35378870458932035$。全程无需展开这个指标对应的斐波那契数。[数值实验](effective_experiment.py) · [各筛界实例](effective_results.json) · [具体指标的 Lean 证书](Gacha/EffectiveWitness.lean)

还可以指出这条路线需要哪项估计才能再增加一个对数。已发表的 Linnik 型定理给出常数 $C,L$，使指定可逆剩余类的最小素数至多为 $CM^L$。吸收常数并调整有限个小模数后，可代入本仓的条件定理得到某个常数 $c>0$ 和任意大的素数指标 $p$ 满足 $P^-(F_p)>c\,p\log p$。本次 Lean 审计覆盖从多项式型素数界到这一结论的蕴含；这一最小公倍数构造给出的无条件下界是 $p\log\log p/20$。另一方面，$2^{K+1}<(K+2)p$ 也已形式化，它限制了完整最小公倍数构造可直接给出的筛界。[形式化的蕴含及构造限制](Gacha/EffectiveSieve.lean) · [Xylouris，定理 1.1](https://www.impan.pl/shop/publication/transaction/download/product/83078)

## 恰好零个或全部根，以及第二个因子位置

上面的根数实验有一个精确解释。当 $p\mid q-\chi_q$，令 $k=(q-\chi_q)/p$。若 $q\mid F_p$，在代数闭包内把 $u^k=r$ 的解映为 $u+u^{-1}$，就得到到 $D_k(z)=-3$ 底域解集的双射。这里 $r\ne r^{-1}$ 排除了把同一条幂方程的两个解错误配成一对；$q\nmid k$ 则保证 $X^k-r$ 恰有 $k$ 个不同根。因此，底域解数等于 $k$ 或 0，分别对应整除或不整除。最大公因式 $\gcd(D_k+3,X^q-X)$ 的次数等于同一数值。[幂方程的单根](Gacha/PowerFiber.lean) · [根集双射与计数](Gacha/DicksonRootCount.lean) · [最大公因式次数](Gacha/DicksonGcd.lean)

对素数指标 $p>5$，令 $q=4p+1$。我们进一步验证了只需一次模幂的充要条件

$$
q\mid F_p\quad\Longleftrightarrow\quad
q\text{ 为素数},\quad p\equiv2\pmod5,\quad 5^p\equiv1\pmod q.
$$

若 $q$ 为合数且整除 $F_p$，其最小素因子至少为 $2p-1$，这与 $q<(2p-1)^2$ 矛盾。素数分支中，整除条件先等价于斐波那契特征根 $a$ 为模 $q$ 非平方。此时 $q\equiv29\pmod{40}$。Lehmer 的五次单位根方法给出 $a$ 为非平方当且仅当 $2a-1$ 为平方，而 $(2a-1)^2=5$。Euler 判据遂化为 $5^p=1$。例如 $p=7$ 时 $5^7\equiv-1\pmod{29}$；$p=37$ 时 $5^{37}\equiv1\pmod{149}$。百万指标范围内的 2,525 个适用素数对都通过了独立模幂核对。[第二位置的完整条件](Gacha/FourBoundary.lean) · [特征比较与模幂证明](Gacha/QuarticCharacter.lean) · [Lehmer 原文](https://www.fq.math.ca/Scanned/4-2/lehmer.pdf) · [计算记录](four_experiment_results.json)

## 改用素数乘积后的下界

对每个固定实数 $A>\log 4$，存在任意大的素数指标 $p$ 满足
\[
 P^-(F_p)>\frac{p\log\log p}{A}.
\]
例如可以取 $A=2$。证明只需令每个素数 $r\le K+1$ 整除 $p-1$。对于 $j\ge3$，从 $j-1$ 和 $j+1$ 各取一个素因子，便能给 $jp-1$ 和 $jp+1$ 各找出一个真因子。因此可用 $M=\prod_{r\le K+1,\ r\ {\rm prime}}r$ 替换最小公倍数。圆分构造仍给出 $M<p\le M^M$，而 $M\le4^{K+1}$。取两次自然对数得到 $\log\log p\le\log M+\log\log M$。对任意给定的 $A>\log 4$，当 $K$ 充分大时，右侧严格小于 $AK$。[素因子同余条件](Gacha/EffectiveSieve.lean) · [素数乘积与增长界](Gacha/PrimorialScreen.lean)

## 用指标的整数表示判断第二个因子位置

对每个素数 $p>5$，有精确等价式
\[
  (4p+1)\mid F_p\quad\Longleftrightarrow\quad
  4p+1\text{ 是素数且存在 }u,v\in\mathbb N,\quad p=u(u+1)+25v^2 .
\]
例如 $37=3\cdot4+25$，$67=6\cdot7+25$；这给出 $149\mid F_{37}$ 和 $269\mid F_{67}$。设 $q=4p+1$。在可能发生整除的分支，$q\equiv29\pmod{40}$，写 $q=a^2+b^2$ 并令 $a$ 为奇数。此时 $b$ 是奇数的两倍。把 $a/b$ 看作模 $q$ 的一个 $-1$ 的平方根，已有的有限域判据化为 $2+a/b$ 是否为平方。用二次互反律分别计算 $a+2b$ 和 $b$ 的雅可比符号，得到这等价于 $5\mid b$，即 $q=x^2+100y^2$。反向中这项表示和 $p,q$ 的素性已经强制 $p\equiv2\pmod5$。最后令奇数 $x=2u+1$。Python 独立枚举整数表示，与模快速倍增的整除检验对照，$7\le p\le10^6$ 的 78,495 个素数指标中，两个方法找到了相同的 1,255 个指标。[雅可比符号计算](Gacha/QuarticForm.lean) · [二次型等价式](Gacha/FourIndexForm.lean) · [Lehmer 原文，定理 2](https://www.fq.math.ca/Scanned/4-2/lehmer.pdf) · [逐项对照结果](four_experiment_results.json)

## 把一般乘数拆成素数幂

设 $q>5$ 是素数，$t=q-(5/q)=kp$，其中 $(5/q)$ 为勒让德符号。对每个素数 $\ell\mid k$，取 $d_\ell=\ell^{v_\ell(k)}$。要判定 $q\mid F_p$，只需分别检验每个 $D_{d_\ell}(X,1)+3$ 在 $\mathbb F_q$ 中是否有根；所有检验都通过，恰好等价于整除。设 $u$ 为两个斐波那契特征根之比，其乘法阶整除 $kp$。对给定的 $\ell$，对应多项式有根，等价于该阶仍整除 $p(k/d_\ell)$。对每个 $\ell$ 都能删掉这部分，恰好说明该阶整除 $p$。因此，原猜想等价于存在任意大的素数指标 $p$，使每个到原检验上界的候选 $q$ 都至少有一个素数幂检验失败。[等价式的 Lean 证明](Gacha/PrimePowerTests.lean)

Python 穷举 $q\le40000$、$2\le k\le100$ 的 2,475 对符合条件的素数 $(p,q)$，其中 1,789 对可以拆成两个或更多素数幂。共做 3,263 次多项式互素检验，372 对在所有分量上都有根，与斐波那契模快速倍增的结果逐对一致。例如 $(p,q)=(37,2221)$ 的乘数为 60，只需检查次数 3、4、5。[实验程序](primary_experiment.py) · [数据](primary_results.json)

## 第三个可能的因子与三次同余

当 $q+1=2mp$、$q\bmod5\in\{2,3\}$，且 $q>5,p>5$ 都为素数、$m$ 为奇数时，已经证明
\[
q\mid F_p \quad\Longleftrightarrow\quad
\exists x\in\mathbb F_q,\quad D_m(x,-1)=1 .
\]
这里 $D_m$ 是第一类 Dickson 多项式。取 $i^2=-1$，用齐次变换 $D_m(ix,1)=i^mD_m(x,-1)$，再利用奇次多项式可以改变符号，便将检验次数从 $2m$ 减半。[奇数半次数公式](Gacha/OddHalf.lean)

特别地，取 $q=6p-1$。对每个素数 $p>5$，$q\mid F_p$ 当且仅当 $q$ 为素数、$p\bmod5\in\{3,4\}$，并且 $x^3+3x=1$ 在 $\mathbb F_q$ 中有解。整除成立时 $q<(2p-1)^2$，因而 $q$ 自身必为素数。在符合素性和剩余类条件的分支，若 $q$ 没有整除 $F_p$，还得到 $5F_p^2\equiv3\bmod q$。这由奇数指标的三倍角恒等式 $F_{3p}=F_p(5F_p^2-3)$ 以及 $q\mid F_{3p}$ 推出。[第三位置三次判据](Gacha/SixthCubic.lean) · [非零余数的平方](Gacha/SixResidue.lean)

Sun 的推论 6.5(ii) 给出了这个位置的另一条整数判据：当 $q=6p-1$ 为素数时，$q\mid F_p$ 等价于 $q=5a^2+108b^2$。Python 逐项比较三次判据、整数表示和 $F_p\bmod q$，遍历 $7\le p\le10^6$ 的 78,495 个素数，三者均得到 3,219 个整除实例。在 9,650 个通过素性和剩余类筛查的实例中，三次式有三个根的有 3,219 个，其余 6,431 个无根。$p=19$ 时，$q=113=5+108$，三个根为 28、41、44。Lean 审计覆盖上段三次判据；整数表示的全范围依据是 Sun 的已发表证明。[Sun，推论 6.5(ii)](https://matwbn.icm.edu.pl/ksiazki/aa/aa84/aa8441.pdf) · [三种方法的独立对照](six_experiment.py) · [结果](six_results.json)

## 一个素数指标超过一千万亿的合数项

取此前构造的素数 $p=1010824870255201$。在 $1\le j\le3000000$ 的 $jp\pm1$ 中，计算找出三个整除 $F_p$ 的数：
\[
54p-1=54584542993780853,\quad
5694p-1=5755636811233114493,\quad
662994p-1=670170824029976731793 .
\]
三个数都在 $(2p-1)^2$ 之下，因此整除性已足以推出它们各自为素数。Lean 采用二进制快速倍增，逐位求 $(F_p,F_{p+1})$ 在各个模数下的余数，分别核验这三个数都整除 $F_p$，且它们的平方都不整除 $F_p$。三者的乘积小于 $p^4\le F_p$，而它们在 $F_p$ 中的指数均为一，故 $F_p$ 至少还有第四个不同的素因子。[内核模运算](Gacha/FastModFib.lean) · [四个不同素因子的证明](Gacha/LargeCofactor.lean) · [搜索程序](large_factor_experiment.py) · [九个指标的计算结果](large_factor_results.json)

该项的最小素因子恰为 $54584542993780853=54p-1$。在已经排除的 $35p$ 与这个候选之间，只需检查 $38p-1,40p+1,48p+1$。第一、三个候选分别可被 677、7 整除，不能是最小素因子。中间候选满足 $F_p\bmod(40p+1)=3925665491575363$。因此首个候选的最小性也通过了内核验证。[精确最小因子](Gacha/HugeLeastFactor.lean)

## 素数指标的有限筛查与平均值界

在 $138\le n\le1000$，如果 $F_n$ 是素数，则 $n$ 必在 $\{359,431,433,449,509,569,571\}$ 中。Lean 对其他素数指标核验了 $2^{F_n}\not\equiv2\pmod{F_n}$，再用素数指标定理处理合数指标。因此 $138\le n\le358$ 无斐波那契素数。证明用二进制模幂逐位平方，检查每段的全部指标。[模幂拒绝条件与可靠性](Gacha/FermatTest.lean) · [有限区间的排除证明](Gacha/PrefixFermat.lean)

另有一个关于剩余类素数总量的估计。给定 $c>1/2$，存在任意大的 $N$ 使 $\sum_{r\le N,\ r\ \mathrm{prime},\ r\equiv1\bmod4}\log r<cN$。如果所有充分大的前缀和都至少为 $cN$，对递减权重 $(n+1)^{-s}$ 作分部求和，就会使归一化 Abel 极限至少为 $c$；模四余一的该极限是 $1/2$。这个结论可用于选择同余筛模数。[有限加权和比较及剩余类估计](Gacha/AbelPrefix.lean)

## 固定线性筛的极限与稀疏模数

记 $S_K=\{p:p\text{ 为素数},\ P^-(F_p)>Kp\}$。对每个固定的自然数 $K$，现在得到完整极限

$$
\lim_{s\downarrow1}(s-1)\sum_{p\in S_K}\frac{\log p}{p^s}=1.
$$

若 $p>5$ 不在 $S_K$ 中，其最小素因子必须是某个 $kp+1$ 或 $kp-1$，其中 $1\le k\le K$。固定 $k$ 和正负号。对任意奇素数 $r\nmid k$，当 $p$ 和 $kp\pm1$ 都是素数且均大于 $r$ 时，$p$ 在模 $r$ 的可逆剩余类中必须避开一个类。中国剩余定理给出有限组筛素数的可用类比例 $\prod_r(r-2)/(r-1)$。素数倒数和发散使该乘积可任意小。每个可逆类的归一化 Abel 权重是其欧拉函数的倒数，有限例外的权重趋于零。最后对 $k$ 与两个符号取有限并，得到补集权重极限为零。这里先固定 $K$，再让 $s$ 从右趋于 1。[极限定理](Gacha/AbelZeroPair.lean) · [剩余类覆盖](Gacha/AbelZeroSlope.lean) · [有限乘积分解](Gacha/MultiCRT.lean)

还可取任意实数 $A>1/2$，使任意给定的 $B$ 以上都有一个素数 $p$ 满足
$$
P^-(F_p)>\frac{p\log\log p}{A}.
$$
令 $M(N)$ 为不超过 $N$ 且模 4 余 1 的全部素数之积，再乘上不超过 $\sqrt N$ 的全部素数。当 $p\equiv1\bmod M(N)$ 时，对候选 $q=jp\pm1$，所需屏蔽的整数 $j\pm1$ 模 4 余 1。如果它是素数，它本身整除 $M(N)$；如果是合数，它的最小素因子至多为 $\sqrt N$。两种情况下都得到 $q$ 的真因子。上一节的剩余类前缀估计给出任意大的端点 $N$，在这些端点 $\log M(N)<cN+\sqrt N\log4$，其中 $1/2<c<A$。取圆分构造给出的 $M(N)<p\le M(N)^{M(N)}$，即可将筛界 $(N-1)p$ 改写成上述关于 $p$ 的不等式。[模数与整除证明](Gacha/MaskedPrimorial.lean) · [增长定理](Gacha/MaskedGrowth.lean)

## 用半指标 Lucas 数证明整项素性

取奇数 $p\ge5$ 和 $k=\lfloor p/4\rfloor$，记 $D=L_{2k+1}=F_{2k}+F_{2k+2}$。Cassini 恒等式给出
$$
F_{4k+1}-1=F_{2k}D,\qquad F_{4k+3}-1=F_{2k+2}D.
$$
两个右端中与 $D$ 相乘的因子都小于 $D$，所以 $D\mid F_p-1$ 且 $D^2>F_p$。由此得到整项素性的等价条件：存在模 $F_p$ 的元素 $w$ 满足 $w^D=1$，而对每个素因子 $r\mid D$，$w^{D/r}-1$ 都是单位。若存在这样的 $w$，对每个素数 $q\mid F_p$，$w$ 模 $q$ 的阶都等于 $D$，故 $D\mid q-1$。这排除了 $q\le\sqrt{F_p}$。反过来，当 $F_p$ 为素数，模 $F_p$ 乘法群的生成元给出见证。在任意指标界以上找到这种证书，与锁定原题等价。[Lean 等价定理](Gacha/HalfLucas.lean) · [Pocklington 原文，1914 年，第 29–30 页](https://upload.wikimedia.org/wikipedia/commons/e/eb/Proceedings_-_Cambridge_Philosophical_Society_%28IA_proceedingscambr18camb%29.pdf)

部分分解也可使用立方根判据。设 $N=dc+1>1$，已证 $d$ 在每个素因子处都保阶，且 $d^3>N$。写 $s=c\bmod d$、$t=\lfloor c/d\rfloor$。若 $N$ 为合数，可取其最小素因子及互补因子，写为 $dx+1$、$dy+1$，其中 $x,y\ge1$。立方界强制 $x+y<d$，故 $s=x+y$、$t=xy$，并有 $s^2=(x-y)^2+4t$。一次整数平方根检查就能排除该情形。这一版本在 Lean 中给出充分条件。[立方根判据](Gacha/CubicOrder.lean) · [Brillhart、Lehmer、Selfridge，1975 年，定理 5](https://electronicsandbooks.com/edt/manual/Magazine/M/Mathematics%20of%20Computation/1960-2002/pdf/1975_v029_n130/2005583.pdf)

Python 从完整的 Lucas 证书递归复核 86 个节点，核验因子乘积、底数模幂和七个斐波那契数的精确值。另用 $w=a^{(F_p-1)/D}\bmod F_p$ 检查半指标证书。按 $p=359,431,433,449,509,569,571$ 的顺序，各需对 $D$ 的 **3、8、5、13、12、14、14** 个不同素因子计算最大公因数，结果均为 1。[Python 复核程序](check_fib_lucas.py) · [证书数据](FibLucasDAG.json)

## 前 1,001 项的完整分类

在 $0\le n\le1000$，$F_n$ 为素数的指标恰为
$$
3,\ 4,\ 5,\ 7,\ 11,\ 13,\ 17,\ 23,\ 29,\ 43,\ 47,\ 83,\ 131,\ 137,\ 359,\ 431,\ 433,\ 449,\ 509,\ 569,\ 571.
$$
对新增的七个正例，Lean 把 86 个 Lucas 证书节点按依赖顺序分批检查，每个已证素数可供后续节点使用。整数与对应斐波那契数之间的等式也分别通过了内核检查。上一节的 Python 程序另对这七项试用部分分解，依次只取 2、3、2、3、2、4、3 个不同素因子便通过立方根判别式检查。[完整分类](Gacha/CertifiedPrefix.lean) · [证书检查器与可靠性定理](Gacha/LucasChecker.lean) · [阶与最大公因数的桥接](Gacha/CubicCertificate.lean)

## 素数的有限对数加权和

为将 Abel 极限与有限求和联系起来，先在 Lean 中建立第一 Mertens 估计 $\sum_{p\le N}(\log p)/p\sim\log N$。交换 $\log(N!)$ 的除数求和顺序后得到 $\sum_{n\le N}\Lambda(n)\lfloor N/n\rfloor$。将取整改为 $N/n$ 引起的总误差在 0 与 $\psi(N)$ 之间。切比雪夫上界、阶乘的 Stirling 下界以及 $N!\le N^N$ 给出 $\log N-1\le\sum_{n\le N}\Lambda(n)/n\le\log N+\log4+4$。再扣去高次素数幂的有界总贡献，即得上述等价式。[有限和与取整界](Gacha/MertensPrefix.lean)

## 从 Abel 极限到有限素数和

固定自然数 $K$。在素数 $p\le X$ 中给每个指标权重 $(\log p)/p$，则有
$$
\lim_{X\to\infty}\frac1{\log X}\sum_{\substack{p\le X\\P^-(F_p)>Kp}}\frac{\log p}{p}=1,
\qquad
\lim_{X\to\infty}\frac1{\log X}\sum_{\substack{p\le X\\P^-(F_p)\le Kp}}\frac{\log p}{p}=0.
$$
在坏指标的无穷级数中取 $s=1+1/\log X$。对所有 $2\le p\le X$，有 $p^{s-1}\le e$，因此坏指标的有限和除以 $\log X$ 至多是相应归一化 Abel 级数的 $e$ 倍，随 $X$ 趋于无穷而趋于零。用上一节的 Mertens 估计减去坏指标权重，即得好指标的等价式。结论采用这里给出的对数权重，筛界中的 $K$ 固定。[有限加权密度](Gacha/FiniteBadLogWeight.lean)

## 指标同余怎样缩短素性证书

设 $p>5$ 为素数，$N=F_p$，正整数 $d$ 与 $p$ 互素。已在模 $N$ 中核实一个阶为 $d$ 且在其所有素因子处保阶的元素。每个素因子 $q\mid N$ 都形如 $q=dx+1$，并且 $q\equiv\pm1\bmod p$。令 $j$ 为 $-2d^{-1}\bmod p$ 的最小非负代表元，则 $x\bmod p$ 只能是 $0$ 或 $j$。因此只要 $N<(dj+1)^2$ 就已证素性。

当 $p\equiv2,3\bmod5$ 时可用更强的不等式。设 $\alpha,\beta$ 是特征方程 $X^2-X-1=0$ 的两个根。在特征 $p$ 下，$(\alpha-\beta)F_p=\alpha^p-\beta^p=(\alpha-\beta)^p$，且 $(\alpha-\beta)^2=5$，从而 $F_p\equiv (5/p)=-1\bmod p$。若 $N$ 为合数，把最小素因子及其互补因子写为 $dx+1,dy+1$，并交换次序，使 $p\mid x$。此时 $x\ge p$、$y\ge j$。于是 $N<(dp+1)(dj+1)$ 已足以判素。[指标剩余类与两种平方根判据](Gacha/RankOrder.lean)

同样的符号条件也能缩小立方根判据所需的 $d$。写 $c=(N-1)/d$。若
$$
N+d^2j^2<1+d^2p+d^3pj,
$$
则 $x+y<dp$。事实上 $(x-j)(y-j)\ge0$ 给出 $j(x+y)\le xy+j^2$，结合 $N=1+d(x+y)+d^2xy$ 即可排除 $x+y\ge dp$。由于 $p\mid x$，商余数给出 $s=c\bmod(dp)=x+y$，$t=\lfloor c/(dp)\rfloor=xy/p$。合数因而强制 $s^2-4pt=(x-y)^2$。排除这一整数平方即可判素。[结合指标的立方根判据](Gacha/RankCubic.lean)

在 $p=433$ 的具体检验中，取 $d=20354267268086208338686180768$。此时 $j=402$，$\lfloor F_{433}/d^3\rfloor=164511$，单用 $d^3>F_{433}$ 的充分条件不适用。Lean 独立核验 $d$ 的素因子、阶见证、大小界和判别式，由上述判据推出 $F_{433}$ 为素数。脚本另记录了七个正例上找到的平方根判据参数。[433 的内核证书](Gacha/RankExample.lean) · [参数搜索](rank_order_experiment.py) · [计算结果](rank_order_results.json)

## 621 位整数 $F_{2971}$ 的内核证书

Williams 先前已证明 $F_{2971}$ 为素数，Dubner 与 Keller 在其斐波那契素数论文中记载了这一结果。这里用可独立重放的部分分解证书核验同一项。[Dubner 与 Keller 的论文](https://citeseerx.ist.psu.edu/document?doi=4df3f6dbcd1c7400e235bac08a8cd9c415b9dd6e&repid=rep1&type=pdf)

利用 $F_{2971}-1=F_{743}L_{743}L_{1485}$ 收集因子。我们将已获得的素数幂按从大到小的顺序相乘，首次越过立方根时得到 209 位的 $d$。它包含 21 个不同的素因子，递归因子证书共有 36 个 Lucas 节点。设 $c=(F_{2971}-1)/d$、$w=2^c\bmod F_{2971}$。Lean 核验了 $w^d=1$、所有 $w^{d/q}-1$ 的单位条件、$d^2<F_{2971}<d^3$，以及 $(c\bmod d)^2-4\lfloor c/d\rfloor$ 为非平方数。最后用二进制倍增验证整数恰等于 $F_{2971}$。Python 独立重算同一份证书；外部因子表只用来寻找候选整数。[Lean 素性定理](Gacha/F2971Result.lean) · [递归因子树](Gacha/F2971Factors.lean) · [模幂与单位条件](Gacha/ResidueCertificate.lean) · [证书数据](fib2971_certificate.json) · [Python 重放](check_fib2971.py) · [候选因子的 FactorDB 条目](https://factordb.com/index.php?id=1100000000193046503)

## 两个自逆余数类的立方根素性判据

设 $p>5$ 为素数，$N=F_p\equiv1\pmod p$。取 $d\mid N-1$、$\gcd(d,p)=1$，并验证上一节的阶证书。令 $T=dp$，$j=(-2d^{-1}\bmod p)$，$B=(1+dj)\bmod T$。每个素因子模 $T$ 都属于 $1,B$ 中的一类，两类各自满足 $b^2\equiv1\pmod T$。由于 $N\equiv1\pmod T$，某个因子在 $b$ 类时，它的互补因子也在 $b$ 类。[余数与互补因子的证明](Gacha/SplitRankCubic.lean)

假设 $N<T^3$ 且 $B\nmid N$。若 $N$ 为合数，把最小素因子与互补因子写成 $b+Tx,b+Ty$，则 $x,y\ge1$。由 $xy+1\ge x+y$，展开乘积可得 $x+y<T$。写 $C=(N-b^2)/T$，于是 $S=(bC\bmod T)=x+y$，$V=(C-bS)/T=xy$。因此某一类必须满足 $S^2=u^2+4V$。分别排除两类的整数解就能断定 $N$ 为素数。实现中的自然数减法在零处截断；一旦存在上述因子对，两处减法都给出通常的整数差。这是自逆余数类的特例。Lenstra 的一般算法处理任意互素余数类，并证明了 $T>N^{1/3}$ 时的多项式时间界。[Lean 判据与平方检验](Gacha/SplitRankCubic.lean) · [Lenstra 原论文](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1984b/art.pdf)

$F_{359}$ 给出了一个可以直接重放的例子。取 $d=21831311678171160001969=1066737847220321\cdot541\cdot181\cdot19\cdot11$，则 $\lfloor F_{359}/d^3\rfloor=45\,691\,809<359^3=46\,268\,279$。Lean 核验阶证书和两个非平方判定，再由本节判据推出素性。Python 还在 $p=431,449,509,569,571$ 找到符合该判据的参数；数据文件给出 $d,B$、模幂见证与两个判别式。[Lean 完整例证](Gacha/SplitRankExample.lean) · [搜索程序](rank_order_experiment.py) · [实验数据](rank_order_results.json)

## 高斯素元与一个二次丢番图方程

令 $z_k=F_{k+1}+iF_k$。它的实部、虚部互素，范数是 $F_{2k+1}$。一般地，若 $a,b$ 是互素自然数且 $a^2+b^2>1$，则 $a+bi$ 在高斯整数中不可约当且仅当 $a^2+b^2$ 为有理素数。对较难的一向，用高斯素元 $a+bi$ 整除其范数，从中取出它整除的有理素数 $q$。若范数为 $q^2$，则 $a+bi$ 与 $q$ 相伴，使 $q$ 同时整除两个坐标，与互素性矛盾。这样原题等价于存在任意大的 $k$，使 $2k+1$ 为素数且 $z_k$ 不可约。[范数、原始坐标与原题的等价式](Gacha/GaussianFib.lean)

这列高斯整数的坐标也可完全用整数方程识别。所有满足 $0\le Y\le X$ 和 $|X^2-XY-Y^2|=1$ 的自然数对恰为 $(F_{k+1},F_k)$。正向识别使用严格递降，反向由 Cassini 恒等式得到。原题因而要求在这组明确分类的整点内证明素范数无界。[整点分类](Gacha/GaussianFib.lean)

## 在同一个加权极限中让筛界趋于无穷

前述每个固定 $K$ 的极限还给出一个统一结论。存在非递减且趋于无穷的整数函数 $f$，使得对 $p\le X$ 加上更强的限制 $P^-(F_p)>p f(X)$ 后，$\sum (\log p)/p$ 除以 $\log X$ 仍趋于 1。将条件换为 $P^-(F_p)>p f(p)$ 也有同样的极限。证明先对每个 $k$ 选出阈值 $T_k$，使 $X\ge T_k$ 时归一化权重与 1 的距离小于 $1/(k+1)$。在 $k\le X$ 中选满足 $T_k\le X$ 的最大值即可。这个构造没有给出 $f$ 的显式增长速度。[对角选择与两种加权极限](Gacha/MovingDensity.lean)

对有限的普通计数，本轮又核验了一个双符号覆盖。设 $p>\max(5,y)$，若 $P^-(F_p)\le Kp$，则存在偶数 $1\le k\le K$ 使 $kp+1$ 或 $kp-1$ 为大于 $y$ 的素数。因此坏指标的个数有一个对偶数 $k$ 的素数对计数上界。取 $P=\prod_{\ell\le y,\ \ell\text{ prime}}\ell$ 与 $k'=k(2P-1)$，则 $k'\equiv-k\pmod P$。对每个 $r\mid P$，有 $r\mid k'\iff r\mid k$；当 $kn>0$ 时，$\gcd(n(kn-1),P)=\gcd(n(k'n+1),P)$。这把负号计数送入相同的正号筛，并保留每个筛素数的局部整除条件。[计数覆盖](Gacha/PairCountBridge.lean) · [变换与最大公因数恒等式](Gacha/MinusPairBridge.lean)

## 两个符号共用的显式 Selberg 上界

取 $P=\prod_{r\le u,\ r\,\mathrm{prime}}r$，筛素数对 $p,kp\pm1$，其中 $p\le X$，两项都大于 $u$，$k$ 为正偶数。记 $\rho_k(d)$ 为 $n(kn+1)\equiv0\bmod d$ 的解数，$\nu_k(d)=\rho_k(d)/d$。对 $r\mid P$，若 $r\mid k$ 则只有零根，否则另一根为 $-k^{-1}$，故 $\rho_k(r)$ 恰为 1 或 2。平方自由模数上的解数相乘。对 $d\mid P$，设 $g_k(d)=\prod_{r\mid d}\nu_k(r)/(1-\nu_k(r))$，并设 $G_k(y)=\sum_{d\mid P,\ d\le y}g_k(d)$。当 $y\ge1$ 时，两个符号的计数之和至多为

$$
2\left(\frac{X+1}{G_k(y)}+(y^2+1)^3[y(y+1)]^2y^2\right).
$$

Lean 直接构造 Selberg 权。对角化后的主项等于 $1/G_k(y)$；过程中的容斥系数在 $d>y^2$ 时消失，因为两个不超过 $y$ 的数的最小公倍数至多是 $y^2$。剩余系数按因子对逐项估计，得到上式中显式的误差多项式。负号反射保留每个素数上的 $\nu_k$，所以也保留整个分母。这些计数包括通过素数对检验后实际并不整除 $F_p$ 的候选。[Selberg 权、主项与显式余项](Gacha/PrimePairQuant.lean) · [两个符号及分母等式](Gacha/ConcretePairCount.lean) · [由计数提取素数指标](Gacha/PairCountWitness.lean)

分母下界的一项有限估计也已形式化。把与偶数 $k$ 互素的 $1\le a,b\le U$ 按 $1/(ab)$ 加权，要求 $ab$ 平方自由，保留下来的质量至少为原质量的四分之一。若 $ab$ 含平方因子，某个奇素数 $r$ 满足 $r^2\mid a$、$r^2\mid b$、或同时 $r\mid a,b$。对固定 $r$，每种情形的权重至多是总权重的 $1/r^2$。这里用到有限调和和的缩放，将被 $d$ 整除的每个 $a$ 送到 $a/d$。最后对所有大于 1 的奇整数求和，用 $4/(2j+3)^2\le1/(j+1)-1/(j+2)$ 望远镜求和得出坏质量不超过四分之三。[平方自由对的有限并集界](Gacha/SquarefreePairMass.lean) · [互素分母上的缩放](Gacha/CoprimePairMass.lean)

## 百万指标内，多少候选素数实际整除斐波那契数？

枚举 $5<p\le10^6$ 的全部 78,495 个素数指标。对每个指标令 $b=\lfloor\log_2p\rfloor$。埃拉托斯特尼筛判定 $q=kp\pm1$ 的素性，二进制倍增直接计算 $F_p\bmod q$。上文的余数定理保证，表中每个给定界限以内的素因子都在枚举范围中。程序先对 $p\le97$ 做整项直接试除，核对三列数据的统计口径。[Python 复现](log_slope_experiment.py) · [各前缀的统计与最小因子示例](log_slope_results.json)

| 最小因子的检验上界 | 至少有一个候选素数的指标 | 确有素因子落在界内的指标 | 最小素因子超过该界的指标 |
| --- | ---: | ---: | ---: |
| $p\lfloor b/2\rfloor$ | 50,598 | 9,509 | 68,986 |
| $pb$ | 71,946 | 11,735 | 66,760 |
| $2pb$ | 78,093 | 14,513 | 63,982 |

在最大的筛界内共有 331,985 对 $(p,q)$。按 $q\bmod 5$ 检查 $kp+1$ 与 $kp-1$ 各自允许的符号后还剩 166,900 对，再要求 $q\equiv1\pmod4$，剩 74,858 对，涉及 52,114 个指标。程序也检验每一个被筛去的候选与 $F_p$ 的整除关系。

在最大的筛界内，只靠素数对条件能确认 402 个指标避开小因子；加入 $F_p\bmod q$ 检验后，这一数目为 63,982。二者的差异给出了改进筛法的具体方向：估计两个线性形式同时为素数后，还需要估计 $q$ 的斐波那契出现秩等于 $p$ 的频率。Sanna 在广义黎曼猜想等条件下研究了固定出现指数的素数分布，其计数允许出现秩为合数。[Sanna 原论文](https://arxiv.org/abs/2212.06127)

## Pell 方程的素数纵坐标

$x^2+4=5y^2$ 的自然数解恰为 $(x,y)=(L_{2j+1},F_{2j+1})$。当 $y\ge2$ 时，考察半整数表达式 $((3x-5y)/2,(3y-x)/2)$。原方程保证两个分子均为偶数；处理 $(4,2)$ 等边界后，递降到较小纵坐标，并可用逆变换重建原解。由此对每个素数 $q>3$，存在非负整数 $x$ 满足 $x^2+4=5q^2$，当且仅当 $q$ 是某个 Fibonacci 值。排除 $q=3$ 正好处理 $F_4$ 的偶指标例外。故原题还等价于该 Pell 方程的素数纵坐标无界。每个这种 $q>3$ 还满足 $q\equiv1\pmod4$。[整点分类、素数等价与模 4 条件](Gacha/PellFib.lean)

## 大素因子界怎样限制因子总重数？

$\Omega(N)$ 表示完整素因子分解的长度，重复因子逐次计数。若 $1\le L\le P^-(F_p)$，则各素因子至少为 $L$，所以 $L^{\Omega(F_p)}\le F_p$。黄金比例 $\varphi$ 满足 $\varphi F_{n+1}+F_n=\varphi^{n+1}$，因此 $F_p\le\varphi^p$。结合所有素数指标 $p>5$ 的下界 $P^-(F_p)\ge2p-1$，得到逐项估计

$$
\Omega(F_p)\le\frac{p\log\varphi}{\log(2p-1)}.
$$

对于通过更强筛界的指标，可以将分母替换为 $\log L$。要由此断定素性，仍需把 $\Omega(F_p)$ 限制到 1。Browning 与 Verzobio 研究了强可除数列上小素因子的筛法；他们的推论 1.3 给出所有自然数指标中相当多的 $n$ 满足 $\Omega(F_n)\le n/\log\log n$，这里的逐项估计使用素数指标特有的因子同余。[Lean 重数界](Gacha/FactorMultiplicity.lean) · [Browning 与 Verzobio 原论文](https://arxiv.org/pdf/2402.19301)

## 无条件的 $p\log p$ 最小素因子下界

**定理。** 对每个自然数 $B$，存在素数 $p>B$ 使得 $F_p$ 的每个素因子 $q$ 都满足 $q>2^{-30}p\log p$。这是关于整项所有素因子的无穷族结论。若要证明所抽原题，仍需使 $F_p$ 本身为素数。[主定理及其全因子表述](Gacha/LogRoughIndices.lean)

把素数 $5<p\le X$ 且 $p>U$ 中满足 $P^-(F_p)\le Kp$ 的指标数记为 $B(X,U,K)$。对每个偶数斜率 $k$，取 $P=\prod_{r\le U}r$（只乘素数）和平方自由分母截止 $Y=U^2$。令 $H$ 为与 $k$ 互素的 $1\le a\le U$ 的倒数和。逐个删去 $k$ 的素因子得 $H\ge(\varphi(k)/k)\log(U+1)$。在 $(a,b)$ 的乘积平方自由时按 $d=ab$ 分组，同一 $d$ 的有序对至多有 $2^{\omega(d)}$ 个。这样的 $d$ 的每个素因子 $r$ 都不整除 $k$，故其 Selberg 局部项为 $2/(r-2)\ge2/r$。结合四分之一的质量下界，得 $G_k(U^2)\ge\frac14(\varphi(k)/k)^2\log^2(U+1)$。[互素调和和](Gacha/TotientHarmonic.lean) · [平方自由整数的因子计数](Gacha/SafePairDenominator.lean) · [实际分母下界](Gacha/PrimePairLocalDen.lean)

逐项展开 $(k/\varphi(k))^2$ 的有限欧拉乘积，按整除条件计数，可得 $\sum_{k\le K}(k/\varphi(k))^2\le e^6K$。将它代入两个符号共用的筛上界，得到对所有 $U\ge1$ 的有限估计

$$
B(X,U,K)\le
  \frac{8e^6 K(X+1)}{\log^2(U+1)}+2K\,E(U^2),\qquad
  E(y)=(y^2+1)^3[y(y+1)]^2y^2.
$$

给定 $B$，选 $K=B+6$、$V=2^{2^{24}K}$、$U=V-1$ 和 $X=V^{64}$。此时 $\log X=64\cdot2^{24}K\log2<2^{30}K$。误差 $E(U^2)\le32U^{24}$；连同被舍去的 $\le U$ 的指标，其总贡献由 $65V^{25}$ 控制。上述显式计数与切比雪夫下界 $\pi(X)\ge(\log2/2)X/\log X$ 留出至少一个素数 $p$，满足 $U<p\le X$ 且 $P^-(F_p)>Kp$。由 $\log p\le\log X$ 即得所述常数。这里的 $X$ 只在证明中选取，计算实验采用的是前节列出的一百万指标范围。[斜率平均](Gacha/TotientMean.lean) · [两符号的求和](Gacha/AveragePairCount.lean) · [数值不等式与常数 $2^{-30}$](Gacha/ExponentialSieveGap.lean)

## Lean 验证

Lean 为 `v4.33.1`，Mathlib 提交为 `0df444a360eaa60ab8c11dca51a86af692955474`，与猜想池锁文件一致。全量 `lake exe cache get` 首次遇到 5 个传输失败，重试后 8,690 个缓存文件全部解压。对较大素数直接试除消耗过多内存，最终构建使用上述短证书。[依赖锁文件](../../lake-manifest.json) · [复现命令](../../README.md#复现本轮)

下列输出来自根目录的 `python scripts/audit.py`，包含 `lake build` 和逐个 `#print axioms`。原题作为命题定义保存。审计对象为本轮证明的定理和引理。

```text
lake build final line: Build completed successfully (3957 jobs).
Raw #print axioms output:
'MathGacha.tendsto_scaled_finiteAbelSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.badFibIndex_progression_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.badFibIndexTerm_le_progressionTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_scaled_finiteLinearPairSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.summable_finiteSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.totalPrimeTerm_eq_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.linearPrimePairTerm_le_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.linearPrimePairTerm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.summable_linearPrimePairTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.summable_exceptionTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.progressionMajorantTerm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.summable_progressionMajorantTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.badFibIndexTerm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.badFibIndexTerm_le_progressionMajorantTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.summable_badFibIndexTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.badFibIndexTsum_le_progressionMajorant' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.exceptionTsum_eq_smallExceptionTsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tsum_progressionMajorant_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_scaled_badFibIndexTsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sieved_add_bad_term_eq_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.summable_sievedTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sievedTsum_add_badFibIndexTsum_eq_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_scaled_sievedTsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.compareWeightedPrefixes' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.abelSeqWeightAntitone' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.abelSeqWeightSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.frequentlyLowPrefixOfAbelLimit' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.quarterLogWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.quarterThetaFrequentlyBelow' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_complexResidueClass_abel_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.re_residueClass_LSeries_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_realResidueClass_abel_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_scaled_nonprimeResidueTsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.summable_primeResidueTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.residueClass_tsum_eq_prime_add_nonprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_primeResidueClass_abel_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.linearFormsClass_sum_le_sieved_add_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.smallClassTerm_le_finiteCap' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.linearFormsSievedWeight_eventually_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_finitePrimeClassMass' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.abelZeroSummableFinsetSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.eventually_candidatePrimeMass_le_classes' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.eventually_candidatePrimeMass_le_classes_except' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_candidatePrimeMass_zero_of_small_class_covers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MathGacha.tendsto_linearPrimePair_plus_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_linearPrimePair_minus_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fullLinearSieveAbelLimit' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fullBadFibIndexAbelLimit' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.exists_plusPair_small_class_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.exists_minusPair_small_class_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_candidatePrimeMass_zero_of_small_class_covers_except' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MathGacha.tendsto_plusPair_abel_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_minusPair_abel_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.averagePairBoundFromDen' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_indices_through_30' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_four_is_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_three_is_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_indices_through_93' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasBasePrimes_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasCertificateTargets_sound' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch00_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch00_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix01_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch01_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch01_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix02_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch02_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch02_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix03_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch03_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch03_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix04_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch04_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch04_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix05_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch05_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch05_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix06_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch06_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch06_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix07_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch07_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch07_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix08_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch08_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch08_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix09_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch09_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch09_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix10_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch10_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch10_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix11_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch11_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch11_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix12_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch12_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch12_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix13_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch13_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch13_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix14_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch14_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch14_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix15_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch15_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch15_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix16_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch16_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch16_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix17_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodeBatch17_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasNodeBatch17_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasNodePrefix18_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasAllNodes_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTargetKnown00_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTarget359_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasTarget359_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTargetKnown01_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTarget431_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasTarget431_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTargetKnown02_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTarget433_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasTarget433_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTargetKnown03_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTarget449_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasTarget449_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTargetKnown04_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTarget509_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasTarget509_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTargetKnown05_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTarget569_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasTarget569_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTargetKnown06_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasTarget571_check' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasTarget571_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibValue359' does not depend on any axioms
'MathGacha.fibValue359_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibValue431' does not depend on any axioms
'MathGacha.fibValue431_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibValue433' does not depend on any axioms
'MathGacha.fibValue433_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibValue449' does not depend on any axioms
'MathGacha.fibValue449_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibValue509' does not depend on any axioms
'MathGacha.fibValue509_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibValue569' does not depend on any axioms
'MathGacha.fibValue569_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibValue571' does not depend on any axioms
'MathGacha.fibValue571_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_indices_through_1000' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairRootCount_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.actualPairSieveNu_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.reflectedPairDenominator_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.actualTwoSlopeBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.finitePairError_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.coprimeDivisorReciprocal_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.coprimePairMass_quarter' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.orderUnitCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.largeOrderCertificateOfChecks' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeOfCubicOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeOfCubicOrderSqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.modulusExponentialLowerBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fourthPowerBelowFib' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.dirichletCutoffBelowSquareRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibRatioData' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.powPredecessorOneIff' depends on axioms: [propext, Quot.sound]
'MathGacha.powSuccessorOneIff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.traceBranchLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibDivisorIffDicksonRootOfBranch' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.frobeniusGcdDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.dicksonFrobeniusGcdDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.traceFiber_fixed_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.traceFiberToRoot_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.natCard_dickson_roots_eq_if_fib_divides' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.oddIndexDyadicCutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeDivisorIffDickson' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffAvoidsDicksonRoots' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.coprimeFrobeniusIffNoRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.avoidsDicksonIffCoprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffCoprimeFrobeniusTests' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.divisorMultiplierResidues' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.noFactorAtTenModTwenty' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'MathGacha.exists_prime_modEq_one_with_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactorAtSmallPrimeCongruences' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactorInOneClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.logLcmUpper' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.loglogBoundForLcmWitness' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.arbitrarilyLargePrimeLeastFactorLogLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.oneClassSizeLimit' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.logGainOfPolynomialProgressionBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.effectiveWitnessPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.effectiveWitnessLeastFactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.eulerPrimeRecNotSummable' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.eulerAllowedRecip_not_summable' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.existsEulerAvoidancePrimes' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibonacciSieveExpSix' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.exponentialSieveGap' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.extractLogRoughFibIndices' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971LeavesPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Known00_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Batch00_check' depends on axioms: [propext, Quot.sound]
'MathGacha.fib2971Batch00_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Known01_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Batch01_check' depends on axioms: [propext, Quot.sound]
'MathGacha.fib2971Batch01_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Known02_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Batch02_check' depends on axioms: [propext, Quot.sound]
'MathGacha.fib2971Batch02_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Known03_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Batch03_check' depends on axioms: [propext, Quot.sound]
'MathGacha.fib2971Batch03_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Known04_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Batch04_check' depends on axioms: [propext, Quot.sound]
'MathGacha.fib2971Batch04_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Known05_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Batch05_check' depends on axioms: [propext, Quot.sound]
'MathGacha.fib2971Batch05_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Known06_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Batch06_check' depends on axioms: [propext, Quot.sound]
'MathGacha.fib2971Batch06_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Known07_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Batch07_check' depends on axioms: [propext, Quot.sound]
'MathGacha.fib2971Batch07_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Known08_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Batch08_check' depends on axioms: [propext, Quot.sound]
'MathGacha.fib2971Batch08_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Certified_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971FactorsPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Unit00' does not depend on any axioms
'MathGacha.fib2971Unit01' does not depend on any axioms
'MathGacha.fib2971Unit02' does not depend on any axioms
'MathGacha.fib2971Unit03' does not depend on any axioms
'MathGacha.fib2971Unit04' does not depend on any axioms
'MathGacha.fib2971Unit05' does not depend on any axioms
'MathGacha.fib2971Unit06' does not depend on any axioms
'MathGacha.fib2971Unit07' does not depend on any axioms
'MathGacha.fib2971Unit08' does not depend on any axioms
'MathGacha.fib2971Unit09' does not depend on any axioms
'MathGacha.fib2971Unit10' does not depend on any axioms
'MathGacha.fib2971Unit11' does not depend on any axioms
'MathGacha.fib2971Unit12' does not depend on any axioms
'MathGacha.fib2971Unit13' does not depend on any axioms
'MathGacha.fib2971Unit14' does not depend on any axioms
'MathGacha.fib2971Unit15' does not depend on any axioms
'MathGacha.fib2971Unit16' does not depend on any axioms
'MathGacha.fib2971Unit17' does not depend on any axioms
'MathGacha.fib2971Unit18' does not depend on any axioms
'MathGacha.fib2971Unit19' does not depend on any axioms
'MathGacha.fib2971Unit20' does not depend on any axioms
'MathGacha.fib2971OrderCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib2971Prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibMulFirstOrder' depends on axioms: [propext, Quot.sound]
'MathGacha.fibQuotientGcd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimePowerAtMultiple' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimePowerAtNeighbors' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.minFactorPower_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_le_goldenRatio_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibMultiplicityLogBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeIndexMultiplicityBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.indexDividesFromCommonFactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimeFactorCongruence' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibLeastFactorLinearBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.divisorProgressionUpTo' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.noSmallFactorFromCompositeForms' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPairMod_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPairMod_first_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.targetBits_value' does not depend on any axioms
'MathGacha.largeIndexDvdIff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.largeIndexFirstDvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.largeIndexSecondDvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.largeIndexThirdDvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.largeIndexCandidateResidue' depends on axioms: [propext, Quot.sound]
'MathGacha.largeIndexExcludesForty' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fermatRejectFalse' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.nonprimeOfFermatReject' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.badFibIndexLogWeight_div_log_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.goodFibIndexLogWeight_div_log_tendsto_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fourBoundaryFibDvdIffNonsquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fourBoundaryQModEight' depends on axioms: [propext, Quot.sound]
'MathGacha.fourBoundaryFibDvdOfNonsquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fourBoundaryPrimeOfDvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fourBoundaryCriterion' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.odd_square_mod8' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sumSquareRepresentation' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.representation_has_odd_coordinate' depends on axioms: [propext, Quot.sound]
'MathGacha.even_coordinate_of_odd_left' depends on axioms: [propext, Quot.sound]
'MathGacha.even_square_half_is_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.orientedSumSquareRepresentation' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.coordinateRootMinusOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.secondFactorShapeArithmetic' depends on axioms: [propext, Quot.sound]
'MathGacha.primeTwoSquareCoprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.evenCoordinateNonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fourNeighborDvdIffCoordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.quarterFormIndexIff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.quarterFormForcesClass' depends on axioms: [propext, Quot.sound]
'MathGacha.fourBoundaryDvdIffQuadraticForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fourBoundaryDvdIffIndexForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPowerDifference' depends on axioms: [propext, Quot.sound]
'MathGacha.fibRootsFromDiscriminant' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibRootsAtPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibFrobeniusZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.gaussianFibOddEqSqAdd' depends on axioms: [propext, Quot.sound]
'MathGacha.gaussianFibSuccessorCoprime' depends on axioms: [propext, Quot.sound]
'MathGacha.gaussianFibPairNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.gaussianFibValueNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.gaussianFibIrreducibleOfPrimeNorm' depends on axioms: [propext, Quot.sound]
'MathGacha.gaussianFibPrimeDivisorOfNatDivisor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.gaussianFibPairIrreducibleIffNormPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.gaussianFibPrimeIff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.gaussianFibPellIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellPairIsFibonacci' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellPairIffFibonacci' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellPairIffGaussianFibValue' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffUnboundedGaussianFibPrimes' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.orderDividesPrimeFactorSubOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeIffLargeOrderCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.evenCassini' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.oddLucasDivisorProducts' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimeIffOddLucasCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffOddLucasCertificates' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.divisor_in_linear_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.effectiveWitnessMinFac' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.largeIndexMinFactorExact' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'MathGacha.primeBeyondThreeSimpleDivisors' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.largeIndexThreeSimplePrimes' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.largeIndexHasFourthPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'MathGacha.logSieveBadIndexCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.infinitelyOftenLogRoughFibIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.allFactorsLogRoughFibIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasBitsValue_bits' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasPowBits_correct' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasPowBits_nat_correct' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasStepCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasCertificatesCheckAux_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasCertificatesCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasCheck7' depends on axioms: [propext, Quot.sound]
'MathGacha.lucasCheck7_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sparseModulusLogLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactorLogLogHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.maskedResidueProduct_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.maskedModulus_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.maskedPrime_dvd_modulus' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactorBoundOnMaskedClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.factorialLogAsMangoldt' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.mangoldtHarmonicFloorBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.mangoldtHarmonicLogBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeMertensPrefixLogBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.tendsto_primeMertensPrefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.reflectedSlope_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.reflectedSlope_even' depends on axioms: [propext]
'MathGacha.dvdReflectedSlopeIff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.minusPairDvdIffPlus' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.minusPairCoprimeIffPlus' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.reflectedPrimePairSurvives' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.existsGrowingCutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.existsGrowingFullWeightFibSieve' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactorCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactor881' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactor17209' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.multiCRTCardAffineUnitAvoiders' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.multiCRTCardCrtAffineAvoiders' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.multiCRTCrtUnitEquivNatCast' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.multiCRTTotientModulusEqProd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.multiCRTCrtUnitEquivCoe' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.multiCRTExistsGoodResidueFinset' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.multiCRTGoodResidueFinsetRatio' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.dicksonScaleEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.oddHalfDicksonRootIff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.inertDivisorIffHalfDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.smallFactorIndices_covered' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.smallFactorIndices_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.count_le_unitSiftedSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.plusPairCoprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.largePlusPairIndices_le_siftedSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.largeMinusPairIndices_le_siftedSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.squarePrefix_le_twoPow' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeCountingLowerSix' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.existsLargeGoodFibIndexOfBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellConicBase' depends on axioms: [propext]
'MathGacha.pellConicYTwo' depends on axioms: [propext]
'MathGacha.pellConicDescentIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellConicAscentIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellConicSameParity' depends on axioms: [propext, Quot.sound]
'MathGacha.pellConicHalfDivisibility' depends on axioms: [propext, Quot.sound]
'MathGacha.pellConicBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellConicExistsSmaller' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellConicOddLucasStep' depends on axioms: [propext, Quot.sound]
'MathGacha.pellConicOddFibStep' depends on axioms: [propext, Quot.sound]
'MathGacha.pellConicOddFibPell' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellConicPointsAreOddFibonacci' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellConicPrimeIffFibValue' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellConicOriginalIffPrimeYUnbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pellConicPrimeYModFour' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibState_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibState_succ' depends on axioms: [propext, Quot.sound]
'MathGacha.fibState_step_injective' depends on axioms: [propext, Quot.sound]
'MathGacha.fibState_collision_returns' depends on axioms: [propext, Quot.sound]
'MathGacha.exists_fib_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.no_fib_factor_at_prime_above_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.finite_factors_avoid_square_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pow_fiber_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.natCard_pow_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.not_dvd_multiplier_of_neighbor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fermatScreenTo1000' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimeCandidatesThrough1000' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.noFibPrimeFrom138Through358' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeMemProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.lucasList' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.auxiliaryLucasPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeValue43' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeValue47' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeValue83' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.squarefreePairLocalData' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.actualPairDenLower' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pair_poly_mod_iff_root_residue' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.residue_class_iff_mod_eq' depends on axioms: [propext]
'MathGacha.pairSiftedCount_eq_pairResidueCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairResidueCount_eq_quotient_main_add_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairResidueCount_remainder_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSiftedCount_eq_quotient_main_add_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSiftedCount_real_error_le_rootCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairPoly_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSupport_divisor_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pair_multSum_eq_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pair_sieve_rem_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairZModRoots_card_eq_pairRootResidues' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairZRoot_card_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairZModRoots_card_eq_fintype' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairRootResidues_card_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairRootResidues_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairRootResidues_card_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairRootResidues_prime_card_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairRootResidues_two_card_of_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairRootResidues_prime_card_lt_of_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSieveNu_prime_pos_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSieveNu_isMultiplicative' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeFactor_set_nonempty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairBoundingSieve_rem_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairBoundingSieveEven_rem_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergSieveEven_rem_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.siftedSum_le_mass_div_den_add_error' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergDen_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergTerm_le_den' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairTargetComplement_abs_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pair_complement_mul' depends on axioms: [propext]
'MathGacha.pairInvertedCoefficient_divisor_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sum_divisors_multiples_via_complement' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergWeight_cancel' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergWeight_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairTargetComplement_div_complement' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairInvertedTerm_abs_le_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairInvertedCoefficient_abs_le_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairInvertedCoefficient_eq_zero_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergWeight_eq_zero_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSieveNu_ge_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergWeight_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergWeight_abs_le_global' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairLambdaSquared_zero_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairLambdaSquared_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairInvertedCoefficient_prod_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sum_cutoff_div_constant' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergWeight_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergMuPlus_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelberg_main_eq_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelberg_errSum_le_root_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergEven_sifted_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergEven_errSum_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.pairSelbergEven_sifted_bound_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.dvdIffDeletePrimeComponents' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibDivisorIffPrimePowerTests' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffPrimePowerObstructions' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primorialLogLogBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.leastFactorLogLogPrimorial' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.dicksonFourShiftEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fourthDicksonRootIffSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fiveSquareAtFourModFive' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fourNeighborDvdIffSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.nonsquareFifthRootDiscriminant' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.nonsquareFibRootIffSquareDiscriminant' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibRootNonsquareIffFivePow' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fourBoundaryIffFivePow' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.jacobiSwapOneModFour' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.jacobiResidueFiveSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.jacobiTwoMulOdd_isNegOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sumSquares_mod_fiveSquare' depends on axioms: [propext, Quot.sound]
'MathGacha.jacobiSumSquaresFactorIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.jacobiAtFive' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.jacobiFive_of_sumSquares_mod_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.quadraticChar_two_add_div_eq_jacobi_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.isSquare_two_add_div_iff_five_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimeOfRankCubic' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.rank433Certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.rankCubicExample433' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.rankOrderFactorClasses' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimeOfRankOrderSize' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.inertCompositeRankFactors' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimeOfOppositeRankOrders' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibAtIndexLegendre' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimeOfInertIndexOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffUnboundedPrimeIndices' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffSieveToSquareRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeSquareFibFactorAtNeighbor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibAtPrimeSquarefreeOfNoNeighborSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.residuePower_sound' depends on axioms: [propext, Quot.sound]
'MathGacha.residueUnitTest_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.largeOrderOfResidueTests' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.safe_card_divisors_sqfree' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.safe_selberg_term_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.squarefreePairMass_le_pairSelbergDen' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.screenWitnessesValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.screenTermsComposite' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.survivor101Composite' depends on axioms: [propext]
'MathGacha.survivor101NoSmallDivisor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.rootPowerFib' depends on axioms: [propext, Quot.sound]
'MathGacha.fibNeighborPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeDvdNeighborFib' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_prime_indices_coprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.finite_factors_avoid_fib_prime_indices' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.arbitrarilyLargePrimeFactors' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.candidateA_subset_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.candidateT_subset_L' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.candidateT_eventually_eq_A_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.candidateT_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffUniformFiniteSieve' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.negativeLargeFactorForEveryTail' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibTripleOddResidue' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sixInertResidueAlternatives' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.dicksonSixShiftEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sixthDicksonRootIffCubic' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeDivisorBelowLinearSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sixBoundaryDvdIffCubic' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fib_q_sub_one_dvd_of_five_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.splitPrimeFactorDividesQSubOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sameClassForcesSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.excludeEqualClassFactorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.fibPrimeSplitRankCubic' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.classNonsquareTest_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.split359Certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.splitRankCubicExample359' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.divisorReciprocal_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.squareObstructionMass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.oddSquareReciprocalSum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.nonSquarefreePair_hasOddWitness' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.squareObstructionCovers' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.squareObstructionMass_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.squareObstructionMass_sum_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.squarefreePairMass_quarter' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.minusOneSquareAtOddIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeFactorAtOddIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.coprimeHarmonic_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.badHarmonicMass_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.coprimeHarmonic_prime_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.prime_not_dvd_list_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.coprimeHarmonic_list_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.coprimeHarmonic_squarefreeProduct_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.deletionFactorList_eq_eulerProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.coprimeHarmonic_squarefreeEuler_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.coprimeHarmonic_one_eq_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.eulerCoprimeDensity_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.coprimeHarmonic_lower_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.totientHarmonicRad_eq_radical' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.totientHarmonicRad_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.totientHarmonic_coprime_rad_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.totientHarmonic_radical_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.totientHarmonic_radical_coprime_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.totientHarmonic_coprime_lower_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.card_filter_dvd_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.weight_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sum_multiples_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.weight_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.mean_weight_le_correction' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.telescope_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.telescope_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.correction_all_numbers' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.correction_le_all_numbers' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.mean_weight_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.localWeight_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sum_multiples_localWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.localWeight_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.mean_localWeight_le_correction' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.phiSqExcess_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.phiSqExcess_div_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.phiSq_localCorrection_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.mean_phiSq_localWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.localWeight_eq_totient_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.mean_totient_ratio_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sum_totient_ratio_on_subset_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sum_pair_upper_from_totient_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.exists_good_from_cardinality' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.exists_good_prime_from_pair_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.sum_pair_upper_on_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.finiteField_image_iff_frobenius_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.exists_unit_with_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.inverseTrace_eq_iff_eq_or_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.not_summable_largeLeastFactorWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.wholeTermPrimeThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffUnboundedMangoldtThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.primeMass_eq_indicator' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathGacha.originalIffNotSummableFibPrimeMass' depends on axioms: [propext, Classical.choice, Quot.sound]
Audit passed: lake build; 635 theorem/lemma axiom reports; 93 Lean files scanned.
```
