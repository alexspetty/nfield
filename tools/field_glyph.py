#!/usr/bin/env python3
"""
field_glyph.py — Generate field glyphs for the fractional field program.

Each fraction k/n produces a repetend. The cumulative digital root of the
repetend traces a path through positions 1-9 on a circle (0 at center).
The glyph overlays all n-1 such paths, with coloring by polarity:
  - Red/yellow: clockwise arcs (positive flow)
  - Gray/green: counterclockwise arcs (negative flow)
  - Brown/olive: overlapping directions

Node colors reflect the polarity classification:
  - Yellow: positive poles (digits on the 3 radial)
  - Red: negative poles (digits on the 6 radial)
  - Gray: neutral/structural positions

Usage:
    python3 field_glyph.py 7
    python3 field_glyph.py 17 --prime
    python3 field_glyph.py --catalog 1 30
    python3 field_glyph.py 17 -o glyph_17.png
    python3 field_glyph.py 17 --light

2026 Alexander S. Petty
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
import matplotlib.patheffects as pe
from pathlib import Path
import argparse
import math

OUT_DIR = Path(__file__).parent / 'out'


# ── palettes ──────────────────────────────────────────────

DARK = {
    'bg':           '#0a0a0f',
    'circle_fill':  '#0e0e18',
    'circle_edge':  '#303050',
    'pos_prime':    '#c8b820',     # yellow: prime positive (clockwise)
    'neg_prime':    '#30a060',     # green: prime negative (counterclockwise)
    'overlap_prime':'#607838',     # olive: prime overlap
    'pos_std':      '#c04040',     # red: form positive (clockwise)
    'neg_std':      '#505060',     # dark gray: form negative (counterclockwise)
    'overlap_std':  '#806050',     # brown: form overlap
    'node_pos':     '#c8b820',     # yellow: 3, 5, 6, 9
    'node_neg':     '#c04040',     # red: 2, 4, 8
    'node_neutral': '#808090',     # gray: 1, 7
    'node_text':    '#202020',
    'center_text':  '#404060',
    'title':        '#8888aa',
}

LIGHT = {
    'bg':           '#ffffff',
    'circle_fill':  '#fafaf5',
    'circle_edge':  '#303030',
    'pos_prime':    '#c0a810',     # yellow: prime positive
    'neg_prime':    '#208848',     # green: prime negative
    'overlap_prime':'#607030',     # olive: prime overlap
    'pos_std':      '#c04040',     # red: form positive
    'neg_std':      '#505058',     # dark gray: form negative
    'overlap_std':  '#806048',     # brown: form overlap
    'node_pos':     '#c8b820',     # yellow: 3, 5, 6, 9
    'node_neg':     '#c03030',     # red: 2, 4, 8
    'node_neutral': '#808080',     # gray: 1, 7
    'node_text':    '#202020',
    'center_text':  '#b0b0b0',
    'title':        '#404040',
}

# Node polarity classification (from the numeric polarity diagram)
#   Neutral: 8, 9, 1  (top, cyan)
#   Positive: 2, 3, 4 (right, red/pink)
#   Negative: 5, 6, 7 (left, gray)
NODE_POLARITY = {
    1: 'neutral',
    2: 'neg',
    3: 'pos',
    4: 'neg',
    5: 'pos',
    6: 'pos',
    7: 'neutral',
    8: 'neg',
    9: 'pos',
}


def digital_root(n):
    if n == 0:
        return 0
    r = n % 9
    return r if r != 0 else 9


def cumulative_polarity(digits):
    """Compute cumulative digital root sequence from a list of digits."""
    result = []
    running = 0
    for d in digits:
        running += d
        dr = running % 9
        if dr == 0:
            dr = 9
        result.append(dr)
    return result


def get_repetend_digits(k, n):
    """Compute the repeating digits of k/n via long division.
    Returns the repeating block only, or [] if the fraction terminates."""
    remainder = k % n
    if remainder == 0:
        return []

    seen = {}
    digits = []

    while remainder != 0:
        if remainder in seen:
            cycle_start = seen[remainder]
            return digits[cycle_start:]
        seen[remainder] = len(digits)
        remainder *= 10
        q = remainder // n
        remainder = remainder % n
        digits.append(q)

        if len(digits) > 100000:
            break

    return []  # terminated (remainder hit 0)


def get_all_digits(k, n):
    """Get all decimal digits of k/n (prefix + one cycle of repetend)."""
    remainder = k % n
    if remainder == 0:
        return []

    seen = {}
    digits = []
    pos = 0

    # Integer part: skip (we only want fractional digits)
    remainder = k % n

    while remainder != 0:
        if remainder in seen:
            # Found cycle; digits already include one full cycle
            break
        seen[remainder] = pos
        remainder *= 10
        q = remainder // n
        remainder = remainder % n
        digits.append(q)
        pos += 1

        if pos > 100000:
            break

    # Filter out leading zeros for terminating fractions
    # (keep them, they're real digits)
    return digits if digits else []


def is_prime(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def position_on_circle(digit, radius=1.0):
    """Map digit 1-9 to circle position. 9 at top, clockwise."""
    if digit == 0:
        return (0.0, 0.0)
    angle = math.pi / 2 - (digit - 9) * 2 * math.pi / 9
    return (radius * math.cos(angle), radius * math.sin(angle))


def classify_direction(d1, d2):
    """Clockwise = +1, counterclockwise = -1, self = 0."""
    if d1 == d2 or d1 == 0 or d2 == 0:
        return 0
    diff = (d2 - d1) % 9
    if diff == 0:
        return 0
    return 1 if diff <= 4 else -1


def draw_glyph(ax, n, force_prime=False, pal=None, show_title=True,
               radius=1.0, cx=0, cy=0):
    """Draw a field glyph on the given axes."""

    if pal is None:
        pal = DARK

    prime = force_prime or is_prime(n)

    ax.set_xlim(cx - 1.55, cx + 1.55)
    ax.set_ylim(cy - 1.6, cy + 1.5)
    ax.set_aspect('equal')
    ax.set_facecolor(pal['bg'])
    ax.axis('off')

    # Background circle
    bg = Circle((cx, cy), radius * 1.12, fill=True,
                facecolor=pal['circle_fill'],
                edgecolor=pal['circle_edge'],
                linewidth=1.8, zorder=1)
    ax.add_patch(bg)

    # ROYGBIV orbit colors
    ORBIT_COLORS = [
        '#cc2222',   # red
        '#dd7711',   # orange
        '#ccaa11',   # yellow
        '#22aa44',   # green
        '#2255cc',   # blue
        '#4422aa',   # indigo
        '#8822aa',   # violet
    ]

    # Build paths grouped by orbit
    # Each distinct repetend pattern defines an orbit
    orbit_paths = {}   # repetend_key -> list of paths
    orbit_order = []   # ordered list of unique orbit keys
    open_path = []

    for k in range(1, n):
        all_digits = get_all_digits(k, n)
        rep_digits = get_repetend_digits(k, n)
        if not all_digits:
            continue
        if not rep_digits:
            total = sum(all_digits)
            dr = total % 9
            if dr == 0:
                dr = 9
            open_path.append(dr)
        else:
            if len(rep_digits) >= 2:
                # Identify orbit by the canonical (sorted-min) rotation
                rotations = []
                for start in range(len(rep_digits)):
                    rotations.append(tuple(rep_digits[start:] + rep_digits[:start]))
                orbit_key = min(rotations)
                if orbit_key not in orbit_paths:
                    orbit_paths[orbit_key] = []
                    orbit_order.append(orbit_key)
                orbit_paths[orbit_key].append(rep_digits)

    all_paths = []
    for key in orbit_order:
        all_paths.extend(orbit_paths[key])
    if len(open_path) >= 2:
        all_paths.append(open_path)

    # Build edges per orbit
    orbit_edges = {}  # orbit_index -> set of (edge, direction) pairs
    for oi, key in enumerate(orbit_order):
        orbit_edges[oi] = {}
        for path in orbit_paths[key]:
            for i in range(len(path)):
                d1 = path[i]
                d2 = path[(i + 1) % len(path)]
                if d1 == d2:
                    continue
                edge = (min(d1, d2), max(d1, d2))
                direction = classify_direction(d1, d2)
                if edge not in orbit_edges[oi]:
                    orbit_edges[oi][edge] = {'count': 0, 'dirs': set()}
                orbit_edges[oi][edge]['count'] += 1
                orbit_edges[oi][edge]['dirs'].add(direction)

    # Draw edges: each orbit in its own ROYGBIV color
    # CW = solid, CCW = dashed
    num_orbits = len(orbit_order)
    for oi in range(num_orbits):
        base_color = ORBIT_COLORS[oi % len(ORBIT_COLORS)]
        edges = orbit_edges[oi]
        if not edges:
            continue
        max_count = max(e['count'] for e in edges.values())

        for edge, info in sorted(edges.items(), key=lambda x: x[1]['count']):
            d1, d2 = edge
            x1, y1 = position_on_circle(d1, radius)
            x2, y2 = position_on_circle(d2, radius)
            x1 += cx; y1 += cy
            x2 += cx; y2 += cy

            intensity = info['count'] / max_count
            lw = 1.0 + 1.5 * intensity
            alpha = 0.5 + 0.5 * intensity

            # Offset parallel lines slightly when multiple orbits share an edge
            offset = 0.006 * radius * (oi - (num_orbits - 1) / 2)
            dx = y2 - y1
            dy = x1 - x2
            norm = (dx*dx + dy*dy)**0.5
            if norm > 0:
                dx, dy = dx/norm*offset, dy/norm*offset
            else:
                dx, dy = 0, 0

            dirs = info['dirs']
            both = len(dirs) > 1

            if both:
                # Both directions: draw solid
                ax.plot([x1+dx, x2+dx], [y1+dy, y2+dy],
                        color=base_color, alpha=alpha, linewidth=lw,
                        solid_capstyle='round', zorder=2)
            elif 1 in dirs:
                # CW: solid
                ax.plot([x1+dx, x2+dx], [y1+dy, y2+dy],
                        color=base_color, alpha=alpha, linewidth=lw,
                        solid_capstyle='round', zorder=2)
            else:
                # CCW: dashed
                ax.plot([x1+dx, x2+dx], [y1+dy, y2+dy],
                        color=base_color, alpha=alpha, linewidth=lw,
                        linestyle=(0, (4, 3)),
                        solid_capstyle='round', zorder=2)

    # Count hits per digit position across all paths
    hit_counts = {d: 0 for d in range(1, 10)}
    for path in all_paths:
        for d in path:
            if 1 <= d <= 9:
                hit_counts[d] += 1
    max_hits = max(hit_counts.values()) if any(hit_counts.values()) else 1

    # Draw nodes: size and opacity scale with hit frequency ("fat bins")
    base_node_r = 0.09 * radius
    max_node_r = 0.16 * radius
    for digit in range(1, 10):
        x, y = position_on_circle(digit, radius)
        x += cx; y += cy

        freq = hit_counts[digit] / max_hits if max_hits > 0 else 0
        nr = base_node_r + (max_node_r - base_node_r) * freq
        alpha = 0.5 + 0.5 * freq

        pol = NODE_POLARITY[digit]
        if pol == 'pos':
            nc = pal['node_pos']
        elif pol == 'neg':
            nc = pal['node_neg']
        else:
            nc = pal['node_neutral']

        node = Circle((x, y), nr, fill=True,
                       facecolor=nc, alpha=alpha,
                       edgecolor=pal['circle_edge'],
                       linewidth=1.2, zorder=4)
        ax.add_patch(node)

        ax.text(x, y, str(digit),
                ha='center', va='center',
                fontsize=9, fontweight='bold',
                color=pal['node_text'], zorder=5)

    # Position 0: at the intersection of lines 1→5 and 8→4
    x1p, y1p = position_on_circle(1, radius)
    x5p, y5p = position_on_circle(5, radius)
    x8p, y8p = position_on_circle(8, radius)
    x4p, y4p = position_on_circle(4, radius)

    # Parametric intersection: line 1→5 and line 8→4
    # L1: P = (x1p,y1p) + t*(x5p-x1p, y5p-y1p)
    # L2: P = (x8p,y8p) + s*(x4p-x8p, y4p-y8p)
    dx1 = x5p - x1p; dy1 = y5p - y1p
    dx2 = x4p - x8p; dy2 = y4p - y8p
    denom = dx1 * dy2 - dy1 * dx2
    if abs(denom) > 1e-10:
        t = ((x8p - x1p) * dy2 - (y8p - y1p) * dx2) / denom
        zero_x = cx + x1p + t * dx1
        zero_y = cy + y1p + t * dy1
    else:
        zero_x, zero_y = cx, cy

    # Draw the 1→5 and 8→4 reference lines (thin)
    ax.plot([cx + x1p, cx + x5p], [cy + y1p, cy + y5p],
            color=pal['center_text'], alpha=0.2, linewidth=0.5, zorder=1)
    ax.plot([cx + x8p, cx + x4p], [cy + y8p, cy + y4p],
            color=pal['center_text'], alpha=0.2, linewidth=0.5, zorder=1)

    center_node = Circle((zero_x, zero_y), base_node_r * 0.7, fill=True,
                          facecolor=pal['bg'],
                          edgecolor=pal['center_text'],
                          linewidth=1.0, zorder=3)
    ax.add_patch(center_node)
    ax.text(zero_x, zero_y, '0', ha='center', va='center',
            fontsize=8, color=pal['center_text'], zorder=4)

    # Title
    if show_title:
        label = f'field of {n}'
        ax.text(cx, cy - radius * 1.38, label,
                ha='center', va='center',
                fontsize=10, fontweight='bold',
                color=pal['title'], zorder=5)


def draw_info_panel(ax, n, pal=None):
    """Draw structural info panel alongside the glyph."""
    if pal is None:
        pal = DARK

    ax.set_facecolor(pal['bg'])
    ax.axis('off')

    prime = is_prime(n)
    kind = 'prime' if prime else 'composite'

    # Compute paths for info display
    open_path = []
    closed_paths = []
    for k in range(1, n):
        all_digits = get_all_digits(k, n)
        rep_digits = get_repetend_digits(k, n)
        if not all_digits:
            continue
        if not rep_digits:
            total = sum(all_digits)
            dr = total % 9
            if dr == 0:
                dr = 9
            open_path.append((k, dr))
        else:
            cp = cumulative_polarity(rep_digits)
            closed_paths.append((k, cp))

    tc = pal['title']
    fs = 7.5

    lines = []
    lines.append(f'n = {n}  ({kind})')
    lines.append(f'digital root: {digital_root(n)}')

    if open_path:
        lines.append(f'open fractions: {len(open_path)}')
        op_str = ' '.join(str(dr) for _, dr in open_path)
        lines.append(f'  path: {op_str}')
    if closed_paths:
        lines.append(f'closed fractions: {len(closed_paths)}')
        if closed_paths:
            rep1 = get_repetend_digits(1, n)
            if rep1:
                lines.append(f'  cycle length: {len(rep1)}')

    lines.append('')

    # Show closed paths (up to 20)
    if closed_paths:
        lines.append('closed paths (cumulative polarity):')
        shown = 0
        for k, cp in closed_paths:
            if shown >= 20:
                lines.append(f'  ... ({len(closed_paths) - 20} more)')
                break
            cp_str = ' '.join(str(v) for v in cp)
            lines.append(f'  {k:>3}/{n}: {cp_str}')
            shown += 1

    text = '\n'.join(lines)
    ax.text(0.02, 0.98, text, transform=ax.transAxes,
            ha='left', va='top',
            fontsize=fs, fontfamily='monospace',
            color=tc, zorder=5)


def generate_single(n, output=None, force_prime=False, svg=False, pal=None,
                    show_info=True):
    if pal is None:
        pal = DARK

    # Count fractions for sizing
    num_fracs = sum(1 for k in range(1, n)
                    if get_repetend_digits(k, n) or get_all_digits(k, n))

    # Glyph on top, field tables below
    table_height = max(2, min(8, num_fracs * 0.25))
    fig = plt.figure(figsize=(10, 6 + table_height), facecolor=pal['bg'])
    gs = fig.add_gridspec(2, 2, height_ratios=[6, table_height],
                          hspace=0.3, wspace=0.15)
    ax_glyph = fig.add_subplot(gs[0, :])
    ax_rep = fig.add_subplot(gs[1, 0])
    ax_pol = fig.add_subplot(gs[1, 1])
    draw_glyph(ax_glyph, n, force_prime=force_prime, pal=pal)
    draw_field_tables(ax_rep, ax_pol, n, pal=pal)

    plt.tight_layout(pad=0.5)

    ext = 'svg' if svg else 'png'
    fname = output or str(OUT_DIR / f'glyph_{n}.{ext}')
    Path(fname).parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(fname, format=ext, facecolor=pal['bg'],
                dpi=200, bbox_inches='tight')
    print(f'Saved: {fname}')
    plt.close(fig)


def draw_field_tables(ax_rep, ax_pol, n, pal=None):
    """Draw the field content panels: closed field content by orbit and orientation."""
    ORBIT_COLORS = [
        '#cc2222', '#dd7711', '#ccaa11', '#22aa44',
        '#2255cc', '#4422aa', '#8822aa',
    ]
    OPEN_COLOR = '#888888'
    POL_COLORS = {
        0: '#4488cc', 1: '#ffffff', 2: '#ffffff',
        3: '#a0a0a0', 4: '#ffffff', 5: '#ffffff',
        6: '#cc4444', 7: '#ffffff', 8: '#ffffff',
        9: '#4488cc',
    }

    # Gather open and closed fractions
    open_rows = []
    open_labels = []
    closed_rows = []
    closed_cumpol = []
    closed_labels = []
    closed_reps = []

    for k in range(1, n):
        rep = get_repetend_digits(k, n)
        if rep:
            closed_rows.append(rep)
            closed_cumpol.append(cumulative_polarity(rep))
            closed_labels.append(f'{k}/{n}')
            closed_reps.append(rep)
        else:
            # Terminating: get all digits
            ad = get_all_digits(k, n)
            if ad:
                dr = sum(ad) % 9
                if dr == 0:
                    dr = 9
                open_rows.append((k, dr, ad))
                open_labels.append(f'{k}/{n}')

    # Assign orbits to closed fractions
    orbit_keys = []
    orbit_map = {}
    for i, rep in enumerate(closed_reps):
        rots = [tuple(rep[s:] + rep[:s]) for s in range(len(rep))]
        key = min(rots)
        if key not in orbit_keys:
            orbit_keys.append(key)
        orbit_map[i] = orbit_keys.index(key)

    bg = pal['bg'] if pal else '#ffffff'
    tc_title = pal.get('title', '#404040') if pal else '#404040'

    # Combine: open rows first (gray), then closed rows (ROYGBIV)
    all_labels = []
    all_types = []  # 'open' or orbit index

    for k, dr, ad in open_rows:
        all_labels.append(f'{k}/{n}')
        all_types.append('open')

    for i in range(len(closed_rows)):
        all_labels.append(closed_labels[i])
        all_types.append(orbit_map[i])

    total_rows = len(all_types)

    if total_rows == 0:
        ax_rep.axis('off')
        ax_pol.axis('off')
        return

    # Determine grid width: max of open digit count and closed repetend length
    L_closed = len(closed_rows[0]) if closed_rows else 0
    L_open = max((len(ad) for _, _, ad in open_rows), default=0)
    L = max(L_closed, L_open, 1)

    fs = max(3, min(6, 80 // max(L, total_rows)))

    # LEFT: field content by orbit
    ax_rep.set_xlim(-0.5, L - 0.5)
    ax_rep.set_ylim(total_rows - 0.5, -0.5)
    ax_rep.set_aspect('equal')
    ax_rep.set_facecolor(bg)
    ax_rep.set_title('field content', fontsize=8, color=tc_title)
    ax_rep.set_yticks(range(0, total_rows, max(1, total_rows // 8)))
    ax_rep.set_yticklabels([all_labels[i] for i in range(0, total_rows, max(1, total_rows // 8))], fontsize=5)
    ax_rep.set_xticks(range(0, L, max(1, L // 16)))
    ax_rep.set_xticklabels(range(0, L, max(1, L // 16)), fontsize=4)

    row_idx = 0
    # Open fractions
    for k, dr, ad in open_rows:
        for j in range(L):
            if j < len(ad):
                ax_rep.add_patch(plt.Rectangle((j-0.5, row_idx-0.5), 1, 1,
                    facecolor=OPEN_COLOR, edgecolor='white', linewidth=0.2))
                ax_rep.text(j, row_idx, str(ad[j]), ha='center', va='center',
                    fontsize=fs, color='white', fontweight='bold')
            else:
                ax_rep.add_patch(plt.Rectangle((j-0.5, row_idx-0.5), 1, 1,
                    facecolor='#e8e8e8', edgecolor='white', linewidth=0.2))
        row_idx += 1

    # Closed fractions
    for i in range(len(closed_rows)):
        color = ORBIT_COLORS[orbit_map[i] % len(ORBIT_COLORS)]
        for j in range(L):
            if j < len(closed_rows[i]):
                ax_rep.add_patch(plt.Rectangle((j-0.5, row_idx-0.5), 1, 1,
                    facecolor=color, edgecolor='white', linewidth=0.2))
                ax_rep.text(j, row_idx, str(closed_rows[i][j]), ha='center', va='center',
                    fontsize=fs, color='white', fontweight='bold')
            else:
                ax_rep.add_patch(plt.Rectangle((j-0.5, row_idx-0.5), 1, 1,
                    facecolor='#e8e8e8', edgecolor='white', linewidth=0.2))
        row_idx += 1

    # RIGHT: orientation (cumulative polarity, poles only)
    ax_pol.set_xlim(-0.5, L - 0.5)
    ax_pol.set_ylim(total_rows - 0.5, -0.5)
    ax_pol.set_aspect('equal')
    ax_pol.set_facecolor(bg)
    ax_pol.set_title('orientation', fontsize=8, color=tc_title)
    ax_pol.set_yticks(range(0, total_rows, max(1, total_rows // 8)))
    ax_pol.set_yticklabels([all_labels[i] for i in range(0, total_rows, max(1, total_rows // 8))], fontsize=5)
    ax_pol.set_xticks(range(0, L, max(1, L // 16)))
    ax_pol.set_xticklabels(range(0, L, max(1, L // 16)), fontsize=4)

    row_idx = 0
    # Open fractions: cumulative polarity of their digits
    for k, dr, ad in open_rows:
        cp = cumulative_polarity(ad)
        for j in range(L):
            if j < len(cp):
                val = cp[j]
                ax_pol.add_patch(plt.Rectangle((j-0.5, row_idx-0.5), 1, 1,
                    facecolor=POL_COLORS[val], edgecolor='#e0e0e0', linewidth=0.2))
                tc = '#000000' if POL_COLORS[val] != '#ffffff' else '#999999'
                ax_pol.text(j, row_idx, str(val), ha='center', va='center',
                    fontsize=fs, color=tc, fontweight='bold')
            else:
                ax_pol.add_patch(plt.Rectangle((j-0.5, row_idx-0.5), 1, 1,
                    facecolor='#f0f0f0', edgecolor='#e0e0e0', linewidth=0.2))
        row_idx += 1

    # Closed fractions
    for i in range(len(closed_rows)):
        cp = closed_cumpol[i]
        for j in range(L):
            if j < len(cp):
                val = cp[j]
                ax_pol.add_patch(plt.Rectangle((j-0.5, row_idx-0.5), 1, 1,
                    facecolor=POL_COLORS[val], edgecolor='#e0e0e0', linewidth=0.2))
                tc = '#000000' if POL_COLORS[val] != '#ffffff' else '#999999'
                ax_pol.text(j, row_idx, str(val), ha='center', va='center',
                    fontsize=fs, color=tc, fontweight='bold')
            else:
                ax_pol.add_patch(plt.Rectangle((j-0.5, row_idx-0.5), 1, 1,
                    facecolor='#f0f0f0', edgecolor='#e0e0e0', linewidth=0.2))
        row_idx += 1


def generate_catalog(start, end, output=None, svg=False, pal=None):
    if pal is None:
        pal = DARK
    numbers = list(range(start, end + 1))
    count = len(numbers)
    cols = min(6, count)
    rows = (count + cols - 1) // cols

    fig, axes = plt.subplots(rows, cols,
                              figsize=(cols * 3.0, rows * 3.0),
                              facecolor=pal['bg'])
    if rows == 1 and cols == 1:
        axes = np.array([[axes]])
    elif rows == 1:
        axes = axes.reshape(1, -1)
    elif cols == 1:
        axes = axes.reshape(-1, 1)

    for idx, n in enumerate(numbers):
        r, c = idx // cols, idx % cols
        draw_glyph(axes[r][c], n, pal=pal)

    for idx in range(count, rows * cols):
        r, c = idx // cols, idx % cols
        axes[r][c].set_facecolor(pal['bg'])
        axes[r][c].axis('off')

    plt.tight_layout(pad=0.6)
    ext = 'svg' if svg else 'png'
    fname = output or str(OUT_DIR / f'glyph_catalog_{start}_{end}.{ext}')
    Path(fname).parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(fname, format=ext, facecolor=pal['bg'],
                dpi=200, bbox_inches='tight')
    print(f'Saved: {fname}')
    plt.close(fig)


def generate_comparison(numbers, output=None, svg=False, pal=None):
    if pal is None:
        pal = DARK
    count = len(numbers)
    cols = min(6, count)
    rows = (count + cols - 1) // cols

    fig, axes = plt.subplots(rows, cols,
                              figsize=(cols * 3.5, rows * 3.5),
                              facecolor=pal['bg'])
    if count == 1:
        axes = np.array([[axes]])
    elif rows == 1:
        axes = axes.reshape(1, -1)
    elif cols == 1:
        axes = axes.reshape(-1, 1)

    for idx, n in enumerate(numbers):
        r, c = idx // cols, idx % cols
        draw_glyph(axes[r][c], n, pal=pal)

    for idx in range(count, rows * cols):
        r, c = idx // cols, idx % cols
        axes[r][c].set_facecolor(pal['bg'])
        axes[r][c].axis('off')

    plt.tight_layout(pad=0.6)
    ext = 'svg' if svg else 'png'
    names = '_'.join(str(n) for n in numbers[:4])
    if len(numbers) > 4:
        names += '_etc'
    fname = output or str(OUT_DIR / f'glyph_{names}.{ext}')
    Path(fname).parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(fname, format=ext, facecolor=pal['bg'],
                dpi=200, bbox_inches='tight')
    print(f'Saved: {fname}')
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(
        description='Generate field glyphs for the fractional field program.')

    parser.add_argument('numbers', nargs='*', type=int,
                        help='Numbers to generate glyphs for')
    parser.add_argument('--catalog', nargs=2, type=int,
                        metavar=('START', 'END'),
                        help='Generate catalog from START to END')
    parser.add_argument('--prime', action='store_true',
                        help='Force prime coloring')
    parser.add_argument('-o', '--output', type=str,
                        help='Output filename')
    parser.add_argument('--svg', action='store_true',
                        help='Output as SVG')
    parser.add_argument('--light', action='store_true',
                        help='Light background (matches original style)')
    parser.add_argument('--no-info', action='store_true',
                        help='Glyph only, no info panel')

    args = parser.parse_args()
    pal = LIGHT if args.light else DARK

    if args.catalog:
        generate_catalog(args.catalog[0], args.catalog[1],
                        output=args.output, svg=args.svg, pal=pal)
    elif args.numbers:
        if len(args.numbers) == 1:
            generate_single(args.numbers[0], output=args.output,
                          force_prime=args.prime, svg=args.svg, pal=pal,
                          show_info=not args.no_info)
        else:
            generate_comparison(args.numbers, output=args.output,
                              svg=args.svg, pal=pal)
    else:
        parser.print_help()


if __name__ == '__main__':
    main()
