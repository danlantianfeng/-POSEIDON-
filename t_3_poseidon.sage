from sage.all import *
import time

# ============================================================================
# 全局参数
# ============================================================================
p = 101
alpha = 3
t = 3                     # 状态分支数

# 固定的 3x3 可逆 MDS 矩阵
M = Matrix(GF(p), [[1, 2, 1],
                   [2, 1, 1],
                   [1, 1, 1]])
M_inv = M.inverse()

# ============================================================================
# 正向置换（每轮都有 MDS）
# ============================================================================
def forward(state, round_types, rc):
    s = vector(GF(p), state)
    for r in range(len(round_types)):
        s = s + vector(GF(p), rc[r])            # AddRoundConstants
        if round_types[r] == 'partial':
            s[0] = s[0] ** alpha                # 部分轮仅第一分支
        else:
            for i in range(t):
                s[i] = s[i] ** alpha
        s = M * s                                # MixLayer
    return list(s)

# ============================================================================
# 立方根（gcd(3,100)=1，逆唯一）
# ============================================================================
def cube_root(val):
    if val == 0:
        return GF(p)(0)
    return val ** ((2 * p - 1) // 3)           # 指数 67

# ============================================================================
# 数值逆向（从输出 y 恢复输入，用于验证根）
# ============================================================================
def inverse_from_y(y_vals, round_types, rc):
    s = vector(GF(p), [GF(p)(0)] + [GF(p)(v) for v in y_vals])
    for r in reversed(range(len(round_types))):
        s = M_inv * s
        if round_types[r] == 'partial':
            s[0] = cube_root(s[0])
        else:
            for i in range(t):
                s[i] = cube_root(s[i])
        s = s - vector(GF(p), rc[r])
    return list(s)

# ============================================================================
# 生成保证有解的轮常数（不遍历域元素）
# ============================================================================
def generate_rc_with_solution(round_types):
    num_rounds = len(round_types)
    x_sol = [GF(p)(0)] + [GF(p).random_element() for _ in range(t-1)]

    rc = []
    for _ in range(num_rounds - 1):
        rc.append([randint(1, 100) for _ in range(t)])
    last_rc = [None] + [randint(1, 100) for _ in range(t-1)]
    rc.append(last_rc)

    s = vector(GF(p), x_sol)
    for r in range(num_rounds - 1):
        s = s + vector(GF(p), rc[r])
        if round_types[r] == 'partial':
            s[0] = s[0] ** alpha
        else:
            for i in range(t):
                s[i] = s[i] ** alpha
        s = M * s

    # 解最后一轮第一个常数使输出第一分量为0
    target = -sum(M[0][j] * ((s[j] + rc[-1][j]) ** alpha) for j in range(1, t)) / M[0][0]
    c = cube_root(target) - s[0]
    rc[-1][0] = int(c)
    return rc, x_sol

# ============================================================================
# Cantor‑Zassenhaus 求根
# ============================================================================
def cz_roots(f):
    if f == 0: return []
    sf = f // gcd(f, f.derivative())
    factors = {}
    g = sf.monic()
    deg = 1
    x = f.parent().gen()
    q = f.base_ring().characteristic()
    while g.degree() >= 2 * deg and g.degree() > 0:
        h_pow = pow(x, q ** deg, g) - x
        d = gcd(g, h_pow)
        if d.degree() > 0:
            factors[deg] = d.monic()
            g = (g // d).monic()
        deg += 1
    if g.degree() > 0:
        factors[g.degree()] = g.monic()
    roots = []
    if 1 in factors:
        lin = factors[1]
        if lin.degree() == 1:
            roots.append(-lin[0] / lin[1])
        else:
            def edf(poly, d_edf):
                if poly.degree() == d_edf:
                    return [poly.monic()]
                while True:
                    r = poly.parent()([GF(q).random_element() for _ in range(poly.degree())])
                    if q == 2:
                        h_edf = r
                        for _ in range(d_edf - 1):
                            h_edf = pow(h_edf, 2, poly) + r
                    else:
                        h_edf = pow(r, (q ** d_edf - 1) // 2, poly) - 1
                    fac = gcd(poly, h_edf)
                    if 0 < fac.degree() < poly.degree():
                        return edf(fac, d_edf) + edf(poly // fac, d_edf)
            for fac in edf(lin, 1):
                if fac.degree() == 1:
                    roots.append(-fac[0] / fac[1])
    return roots

# ============================================================================
# 攻击指定轮数
# ============================================================================
def attack_rounds(num_rounds):
    if num_rounds == 1:
        round_types = ['full']
    elif num_rounds == 2:
        round_types = ['full', 'full']
    else:
        RP = num_rounds - 2
        round_types = ['full'] + ['partial'] * RP + ['full']

    print(f"\n{'='*60}")
    print(f"攻击 {num_rounds} 轮 Poseidon (t=3)，轮结构：{round_types}")
    print(f"{'='*60}")

    # ---------- 生成保证有解的轮常数 ----------
    set_random_seed(int(time.time()) % 10000)
    rc, x_sol = generate_rc_with_solution(round_types)
    print("轮常数：", rc)
    print(f"预埋的解: input = {x_sol}")

    # 正向计算得到预埋的输出
    out_sol = forward(x_sol, round_types, rc)
    y_sol = out_sol[1:]   # [y1_sol, y2_sol]
    print(f"预埋的输出 y = [0, {y_sol[0]}, {y_sol[1]}]")

    # ---------- 逆向方程组构建 ----------
    t0 = time.perf_counter()
    num_vars = sum(t if r == 'full' else 1 for r in round_types)
    var_names = ['y1', 'y2'] + [f'z{i}' for i in range(1, num_vars + 1)]
    R = PolynomialRing(GF(p), var_names, order='lex')
    y1, y2 = R('y1'), R('y2')
    z = [R(f'z{i}') for i in range(1, num_vars + 1)]

    state_vec = vector(R, [R(0), y1, y2])
    equations = []
    var_idx = 0
    for r in reversed(range(num_rounds)):
        state_vec = M_inv * state_vec               # InvMDS
        if round_types[r] == 'partial':
            zi = z[var_idx]
            eq = zi**alpha - state_vec[0]
            equations.append(eq)
            state_vec[0] = zi
            var_idx += 1
        else:  # full
            for i in range(t):
                zi = z[var_idx + i]
                eq = zi**alpha - state_vec[i]
                equations.append(eq)
                state_vec[i] = zi
            var_idx += t
        state_vec = state_vec - vector(R, rc[r])    # InvRC
    h = state_vec[0]                                # 约束 input[0] = 0
    t1 = time.perf_counter()
    print(f"逆向方程组构建: {t1 - t0:.4f} 秒，方程数 = {len(equations)}")

    # ---------- 迭代结式消元 ----------
    t0 = time.perf_counter()
    h_current = h
    for i in range(len(equations), 0, -1):
        zi_name = f'z{i}'
        eq = equations[i - 1]
        zi = R(zi_name)
        if h_current.degree(zi) <= 0:
            h_current = h_current ** alpha
        else:
            other_vars = [v for v in R.gens() if str(v) != zi_name]
            if other_vars:
                coeff_ring = PolynomialRing(GF(p), [str(v) for v in other_vars], order='lex')
                R_univ = PolynomialRing(coeff_ring, zi_name)
            else:
                R_univ = PolynomialRing(GF(p), zi_name)
            h_univ = R_univ(h_current.polynomial(zi))
            eq_univ = R_univ(eq.polynomial(zi))
            res = h_univ.resultant(eq_univ)
            h_current = R(res) if other_vars else R(GF(p)(res))
    t1 = time.perf_counter()
    print(f"结式消元: {t1 - t0:.4f} 秒")

    remaining = [str(v) for v in h_current.variables()]
    print(f"消元后剩余变量: {remaining}")

    # ---------- 固定 y2 为预埋值，得到关于 y1 的单变量多项式 ----------
    h_y1 = h_current.subs({R('y2'): y_sol[1]})
    Ry = PolynomialRing(GF(p), 'y1')
    y1_var = R('y1')
    d = h_y1.degree(y1_var)
    if d < 0:
        print("h_y1 退化为常数，可能无解")
        return
    coeffs = [GF(p)(h_y1.coefficient({y1_var: j})) for j in range(d + 1)]
    h_uni = Ry(coeffs)
    print(f"固定 y2 = {y_sol[1]} 后，关于 y1 的多项式次数: {h_uni.degree()}")

    # ---------- Cantor‑Zassenhaus 求根 ----------
    t0 = time.perf_counter()
    roots_y1 = cz_roots(h_uni)
    t1 = time.perf_counter()
    print(f"求根: {t1 - t0:.4f} 秒，根 y1 = {roots_y1}")

    # ---------- 恢复原像并验证 ----------
    t0 = time.perf_counter()
    found = False
    for y1_val in roots_y1:
        y_vals = [y1_val, y_sol[1]]
        s = inverse_from_y(y_vals, round_types, rc)
        x_recovered = s[1:]   # 输入的第2,3分量
        out_check = forward([0] + x_recovered, round_types, rc)
        if out_check[0] == 0 and out_check[1] == y1_val and out_check[2] == y_sol[1]:
            print(f"  ✓ CICO 解: x = {[0] + x_recovered}, y = [0, {y1_val}, {y_sol[1]}]")
            found = True
    if not found:
        print("  未找到有效解")
    t1 = time.perf_counter()
    print(f"原像验证: {t1 - t0:.4f} 秒")

# ============================================================================
# 执行 1～3 轮攻击
# ============================================================================
print("开始攻击 1～3 轮 Poseidon (t=3)")
print("域：GF(101)，α = 3，分支数 t = 3")
for r in range(1, 4):
    attack_rounds(r)
