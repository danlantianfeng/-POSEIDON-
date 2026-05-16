import math

def attack_complexity(t, total_rounds, alpha=3, calibrate=True):
    """
    参数:
        t            : 状态分支数
        total_rounds : 总轮数
        alpha        : S 盒指数（默认 3）
        calibrate    : 是否使用实验校准的 dP(h) ≈ 1/9
    """
    # 根据总轮数确定完整轮数 RF（标准 HADES 要求 RF 为偶数）
    if total_rounds == 1:
        RF = 1          # 单轮只能是 1 个完整轮
        RP = 0
    else:
        RF = 2          # 标准设置：首尾各 1 个完整轮
        RP = total_rounds - RF   # 中间部分轮数
    
    # 中间变量数 n = 所有逆 S 盒数量
    n = RF * t + RP
    
    # 加权度 dP(h) 实验校准值（对于 t=2, RF=2 的情况测定为 1/9）
    if calibrate:
        dP_h = 1.0 / 9.0
    else:
        dP_h = 1.0    # 保守估计
    
    base = 2 * alpha - 1       # α=3 时 base=5
    ops = dP_h * (base ** (n + 2))
    log2_cost = math.log2(ops) if ops > 0 else 0
    return log2_cost


def security_level(t, total_rounds, alpha=3, field_bits=256):
    """
    估算大域（如 256 位）下的等效安全位数
    将小域 GF(101) 上的复杂度按域比特长度比例放大
    """
    log2_small = attack_complexity(t, total_rounds, alpha, calibrate=True)
    small_field_bits = math.log2(101)
    return log2_small * (field_bits / small_field_bits)


if __name__ == "__main__":
    print("改进结式攻击复杂度估计（修正 n 计算）\n")
    for r in range(1, 7):
        log2c = attack_complexity(t=2, total_rounds=r, alpha=3)
        n = (1 if r==1 else 2)*2 + max(0, r-2)  # 手动计算一下用于显示
        print(f"t=2, 轮数 {r}: n={n}, log2 ≈ {log2c:.2f}")

    print("\n大域 (256 位) 等效安全位 (t=2):")
    for r in range(1, 6):
        sec = security_level(t=2, total_rounds=r, alpha=3, field_bits=256)
        print(f"轮数 {r}: ≈ {sec:.1f} 位")

    print("\n--- t=3 示例 ---")
    for r in range(1, 5):
        log2c = attack_complexity(t=3, total_rounds=r, alpha=3)
        n = (1 if r==1 else 2)*3 + max(0, r-2)
        print(f"t=3, 轮数 {r}: n={n}, log2 ≈ {log2c:.2f}")
