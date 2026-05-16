from sage.all import *
import time

# ============================================================================
# 域选择 —— 修改此处切换小域/大域
# ============================================================================
USE_LARGE_FIELD = True  # True: 256位大域, False: GF(101)小域

if USE_LARGE_FIELD:
    # 动态生成满足 gcd(3, p-1)=1 的 256 位素数
    print("正在寻找满足 gcd(3, p-1)=1 的 256 位素数...")
    while True:
        PRIME = random_prime(2^256, proof=False, lbound=2^255)
        if gcd(3, PRIME - 1) == 1:
            break
    print(f"选定素数: {PRIME}")
else:
    PRIME = 101

F = GF(PRIME)
ALPHA = 3
T = 2                     # 分支数

assert gcd(ALPHA, PRIME - 1) == 1, "alpha 必须与 p-1 互质"

print(f"工作域: GF({PRIME})  (比特长度: {PRIME.nbits()})")
print(f"alpha={ALPHA}, t={T}")

# ============================================================================
# 基本工具
# ============================================================================

def cube_root(val):
    """通用立方根，利用 1/3 mod (p-1)"""
    if val == 0:
        return F(0)
    exp = inverse_mod(ALPHA, PRIME - 1)
    return val ** exp

# 固定的 2x2 MDS 矩阵 (在任意域上均可逆)
M = Matrix(F, [[1, 2], [2, 1]])
M_inv = M.inverse()

# ============================================================================
# 正向置换
# ============================================================================
def forward(state, round_types, rc):
    s = vector(F, state)
    for r in range(len(round_types)):
        s = s + vector(F, rc[r])
        if round_types[r] == 'partial':
            s[0] = s[0] ** ALPHA
        else:
            for i in range(T):
                s[i] = s[i] ** ALPHA
        s = M * s
    return list(s)

# ============================================================================
# 数值逆向 (用于验证)
# ============================================================================
def inverse_from_y(y_val, round_types, rc):
    s = vector(F, [F(0), y_val])
    for r in reversed(range(len(round_types))):
        s = M_inv * s
        if round_types[r] == 'partial':
            s[0] = cube_root(s[0])
        else:
            for i in range(T):
                s[i] = cube_root(s[i])
        s = s - vector(F, rc[r])
    return list(s)

# ============================================================================
# 生成有解的轮常数 (不遍历域元素)
# ============================================================================
def generate_rc_with_solution(round_types):
    num_rounds = len(round_types)
    x_sol = F.random_element()

    rc = []
    for _ in range(num_rounds - 1):
        rc.append([F.random_element() for _ in range(T)])
    last_rc = [None] + [F.random_element() for _ in range(T - 1)]
    rc.append(last_rc)

    # 正向至最后一轮加常数前
    s = vector(F, [F(0), x_sol])
    for r in range(num_rounds - 1):
        s = s + vector(F, rc[r])
        if round_types[r] == 'partial':
            s[0] = s[0] ** ALPHA
        else:
            for i in range(T):
                s[i] = s[i] ** ALPHA
        s = M * s

    # 解最后一轮第一常数使输出第一分量为0
    target = - (M[0][1] * ((s[1] + rc[-1][1]) ** ALPHA)) / M[0][0]
    rc[-1][0] = int(cube_root(target) - s[0])
    return rc, x_sol

# ============================================================================
# Cantor‑Zassenhaus 求根 (适用于任意有限域)
# ============================================================================
def cz_roots(f):
    if f == 0: return []
    sf = f // gcd(f, f.derivative())
    factors = {}
    g = sf.monic()
    deg = 1
    x = f.parent().gen()
    q = F.cardinality()
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
                    r = poly.parent()([F.random_element() for _ in range(poly.degree())])
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
    print(f"攻击 {num_rounds} 轮 Poseidon (t=2)，轮结构：{round_types}")
    print(f"{'='*60}")

    # ---------- 生成轮常数 ----------
    t0 = time.perf_counter()
    rc, x_sol = generate_rc_with_solution(round_types)
    out_sol = forward([0, x_sol], round_types, rc)
    y_sol = out_sol[1]
    t1 = time.perf_counter()
    print(f"轮常数生成: {t1 - t0:.4f} 秒")
    print(f"预埋解: x={x_sol}, y={y_sol}")

    # ---------- 逆向方程组构建 ----------
    t0 = time.perf_counter()
    num_vars = sum(T if r == 'full' else 1 for r in round_types)
    var_names = ['y'] + [f'z{i}' for i in range(1, num_vars + 1)]
    R = PolynomialRing(F, var_names, order='lex')
    y = R('y')
    z = [R(f'z{i}') for i in range(1, num_vars + 1)]

    state_vec = vector(R, [R(0), y])
    equations = []
    var_idx = 0
    for r in reversed(range(num_rounds)):
        state_vec = M_inv * state_vec               # InvMDS
        if round_types[r] == 'partial':
            zi = z[var_idx]
            eq = zi**ALPHA - state_vec[0]
            equations.append(eq)
            state_vec[0] = zi
            var_idx += 1
        else:  # full
            for i in range(T):
                zi = z[var_idx + i]
                eq = zi**ALPHA - state_vec[i]
                equations.append(eq)
                state_vec[i] = zi
            var_idx += T
        state_vec = state_vec - vector(R, rc[r])    # InvRC
    h = state_vec[0]                                # 约束 input[0] = 0
    t1 = time.perf_counter()
    print(f"逆向方程组构建: {t1 - t0:.4f} 秒 (方程数: {len(equations)})")

    # ---------- 迭代结式消元 ----------
    t0 = time.perf_counter()
    h_current = h
    for i in range(len(equations), 0, -1):
        zi_name = f'z{i}'
        eq = equations[i - 1]
        zi = R(zi_name)
        if h_current.degree(zi) <= 0:
            h_current = h_current ** ALPHA
        else:
            other_vars = [v for v in R.gens() if str(v) != zi_name]
            if other_vars:
                coeff_ring = PolynomialRing(F, [str(v) for v in other_vars], order='lex')
                R_univ = PolynomialRing(coeff_ring, zi_name)
            else:
                R_univ = PolynomialRing(F, zi_name)
            h_univ = R_univ(h_current.polynomial(zi))
            eq_univ = R_univ(eq.polynomial(zi))
            res = h_univ.resultant(eq_univ)
            h_current = R(res) if other_vars else R(F(res))
    t1 = time.perf_counter()
    print(f"结式消元: {t1 - t0:.4f} 秒")

    # 提取单变量多项式
    Ry = PolynomialRing(F, 'y')
    y_var = R('y')
    d = h_current.degree(y_var)
    coeffs = [F(h_current.coefficient({y_var: j})) for j in range(d + 1)]
    h_uni = Ry(coeffs)
    print(f"单变量多项式 h(y) 次数: {h_uni.degree()}")

    # ---------- 求根 ----------
    t0 = time.perf_counter()
    roots_y = cz_roots(h_uni)
    t1 = time.perf_counter()
    print(f"求根: {t1 - t0:.4f} 秒, 根 y = {roots_y}")

    # ---------- 恢复原像并验证 ----------
    t0 = time.perf_counter()
    found = False
    for yv in roots_y:
        s = inverse_from_y(yv, round_types, rc)
        xv = s[1]
        out_check = forward([0, xv], round_types, rc)
        if out_check[0] == 0 and out_check[1] == yv:
            print(f"  ✓ CICO 解: x = {xv}, y = {yv}")
            found = True
    if not found:
        print("  未找到有效解")
    t1 = time.perf_counter()
    print(f"原像验证: {t1 - t0:.4f} 秒")

# ============================================================================
# 执行
# ============================================================================
for r in range(1, 6):
    attack_rounds(r)
