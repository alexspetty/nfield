import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import sys

def get_repetend(k, n, base=10):
    remainder = k % n
    seen = {}
    digits = []
    while remainder != 0:
        if remainder in seen:
            return digits[seen[remainder]:]
        seen[remainder] = len(digits)
        remainder *= base
        digits.append(remainder // n)
        remainder = remainder % n
    return []

def cumulative_polarity(digits, base=10):
    result = []
    running = 0
    for d in digits:
        running += d
        dr = running % (base - 1)
        if dr == 0:
            dr = base - 1
        result.append(dr)
    return result

def make_aztec_rug(n, base=10, output='aztec_rug.png'):
    rows_digits = []
    rows_cumpol = []
    labels = []

    for k in range(1, n):
        rep = get_repetend(k, n, base)
        if not rep:
            continue
        rows_digits.append(rep)
        rows_cumpol.append(cumulative_polarity(rep, base))
        labels.append(f'{k}/{n}')

    if not rows_digits:
        print(f'No closed fractions for n={n}')
        return

    L = len(rows_digits[0])
    num_rows = len(rows_digits)
    digit_grid = np.array(rows_digits)
    cumpol_grid = np.array(rows_cumpol)

    # ROYGBIV orbit colors
    ORBIT_COLORS = [
        '#cc2222', '#dd7711', '#ccaa11', '#22aa44',
        '#2255cc', '#4422aa', '#8822aa',
    ]

    # Assign each fraction to its orbit
    orbit_keys = []
    orbit_map = {}
    for i, rep in enumerate(rows_digits):
        rotations = [tuple(rep[s:] + rep[:s]) for s in range(len(rep))]
        key = min(rotations)
        if key not in orbit_keys:
            orbit_keys.append(key)
        orbit_map[i] = orbit_keys.index(key)

    # Cumulative polarity: three poles
    # 0,9 = blue (neutral) | 3 = gray (positive) | 6 = red (negative)
    # Only three colors: the poles. Form numbers get white (empty).
    pol_colors = {
        0: '#4488cc',  # blue (neutral)
        1: '#ffffff',  # form (empty)
        2: '#ffffff',  # form
        3: '#a0a0a0',  # gray (positive pole)
        4: '#ffffff',  # form
        5: '#ffffff',  # form
        6: '#cc4444',  # red (negative pole)
        7: '#ffffff',  # form
        8: '#ffffff',  # form
        9: '#4488cc',  # blue (neutral, same as 0)
    }

    fig, (ax1, ax2) = plt.subplots(1, 2,
        figsize=(max(L*0.35, 6)*2, num_rows*0.35 + 1))
    fig.patch.set_facecolor('white')
    fs = max(4, min(7, 120 // L))

    # LEFT: repetend colored by orbit (ROYGBIV)
    ax1.set_xlim(-0.5, L - 0.5)
    ax1.set_ylim(num_rows - 0.5, -0.5)
    ax1.set_aspect('equal')
    ax1.set_title(f'field of {n}: repetend (orbits)', fontsize=10, fontweight='bold')
    ax1.set_ylabel('k/n')
    ax1.set_yticks(range(0, num_rows, max(1, num_rows // 10)))
    ax1.set_yticklabels([labels[i] for i in range(0, num_rows, max(1, num_rows // 10))], fontsize=6)
    ax1.set_xticks(range(L))
    ax1.set_xticklabels(range(L), fontsize=5)

    for i in range(num_rows):
        color = ORBIT_COLORS[orbit_map[i] % len(ORBIT_COLORS)]
        for j in range(L):
            ax1.add_patch(plt.Rectangle((j-0.5, i-0.5), 1, 1,
                facecolor=color, edgecolor='white', linewidth=0.3))
            ax1.text(j, i, str(digit_grid[i, j]), ha='center', va='center',
                fontsize=fs, color='white', fontweight='bold')

    # RIGHT: cumulative polarity colored by polarity (blue/gray/red)
    ax2.set_xlim(-0.5, L - 0.5)
    ax2.set_ylim(num_rows - 0.5, -0.5)
    ax2.set_aspect('equal')
    ax2.set_title(f'field of {n}: cumulative polarity (mod {base-1})', fontsize=10, fontweight='bold')
    ax2.set_yticks(range(0, num_rows, max(1, num_rows // 10)))
    ax2.set_yticklabels([labels[i] for i in range(0, num_rows, max(1, num_rows // 10))], fontsize=6)
    ax2.set_xticks(range(L))
    ax2.set_xticklabels(range(L), fontsize=5)

    for i in range(num_rows):
        for j in range(L):
            val = cumpol_grid[i, j]
            ax2.add_patch(plt.Rectangle((j-0.5, i-0.5), 1, 1,
                facecolor=pol_colors[val], edgecolor='white', linewidth=0.3))
            ax2.text(j, i, str(val), ha='center', va='center',
                fontsize=fs, color='black', fontweight='bold')

    plt.tight_layout()
    plt.savefig(output, dpi=150, bbox_inches='tight')
    print(f'Saved: {output}')

n = int(sys.argv[1]) if len(sys.argv) > 1 else 17
make_aztec_rug(n)
