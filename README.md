# AI Math Paper Gacha · 数学论文抽卡

> **AI-Generated Math Gacha Disclaimer**
>
> **100% AI 自动生成的数学论文抽卡实验（AI-Generated Math Gacha）**
>
> Agent 为 OpenAI Codex（GPT-6）。本轮运行于 2026-11-27，验证状态为 **Partial**。

## 抽卡记录

| 题号 | 方向 | 状态 | 结论 | Lean 入口 |
| --- | --- | --- | --- | --- |
| [FibonacciPrimes · 研究报告](attempts/FibonacciPrimes/REPORT.md) | 初等数论 | **Partial** | 对任意 $A>1/2$，有任意大的素数 $p$ 满足 $P^-(F_p)>p\log\log(p)/A$，其中 $P^-$ 表示最小素因子。对每个固定 $K$，满足 $P^-(F_p)>Kp$ 的素数指标的归一化 Abel 权重趋于 1。同一集合在有限和 $\sum_{p\le X}(\log p)/p$ 中的相对权重也趋于 1。621 位的 $F_{2971}$ 已核验证书。无限性仍待证明。 | [Gacha.lean](attempts/FibonacciPrimes/Gacha.lean) |

## 复现本轮

在仓库根目录运行以下命令。Lean 使用锁定的 4.33.1 工具链，Python 脚本只使用标准库。

```sh
lake exe cache get
lake build
python scripts/audit.py
python attempts/FibonacciPrimes/experiment.py
python attempts/FibonacciPrimes/linear_experiment.py
python attempts/FibonacciPrimes/boundary_experiment.py
python attempts/FibonacciPrimes/dickson_experiment.py
python attempts/FibonacciPrimes/polynomial_gcd_experiment.py
python attempts/FibonacciPrimes/four_experiment.py
python attempts/FibonacciPrimes/six_experiment.py
python attempts/FibonacciPrimes/primary_experiment.py
python attempts/FibonacciPrimes/large_factor_experiment.py
python attempts/FibonacciPrimes/effective_experiment.py
python attempts/FibonacciPrimes/lucas_certificates.py
python attempts/FibonacciPrimes/check_fib_lucas.py
python attempts/FibonacciPrimes/check_fib2971.py
python attempts/FibonacciPrimes/rank_order_experiment.py
python scripts/draw.py --receipt d1
```

审计逐项打印定理的公理依赖。核对原题时，另取一份含固定提交的猜想池克隆。

```sh
git clone https://github.com/google-deepmind/formal-conjectures.git ../formal-conjectures
python scripts/check_statement.py ../formal-conjectures attempts/FibonacciPrimes
```

原题来自 The Formal Conjectures Authors。原始命题及其出处见[固定版本源码](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/FibonacciPrimes.lean#L28-L38)。代码采用 [Apache License 2.0](LICENSE)。
