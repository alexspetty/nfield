#!/usr/bin/env python3
"""
Signal-to-noise ratio: |b*F0*Q| vs |b^2*coupling|.
Does their ratio scale like log(b)?
"""
import cmath, math

def compute_snr(b):
    m = b * b

    # Generator and dlogs
    units = [a for a in range(1, m) if math.gcd(a, m) == 1]
    phi = len(units)

    g = None
    for c in range(2, m):
        if math.gcd(c, m) != 1: continue
        v, o = 1, 0
        while True:
            v = v * c % m
            o += 1
            if v == 1: break
        if o == phi:
            g = c
            break

    dlog = {}
    v = 1
    for k in range(phi):
        dlog[v] = k
        v = v * g % m

    dl_m1 = dlog[m - 1]
    odd_j = [j for j in range(phi) if (2 * j * dl_m1) % (2 * phi) == phi]

    results = []
    for j in odd_j:
        w = cmath.exp(2j * cmath.pi / phi)

        # chi_bar(k) for k=1..b-1
        chi_bar = {}
        for k in range(1, b):
            if k in dlog:
                chi_bar[k] = w**(-j * dlog[k])

        # Fine subgroup character
        psi = {}
        for l in range(b):
            elem = (1 + l * b) % m
            if elem in dlog:
                psi[l] = w**(-j * dlog[elem])
            else:
                psi[l] = 0

        # F0 = sum l * psi(l)
        F0 = sum(l * psi[l] for l in range(b))

        # Q = sum k * chi_bar(k)
        Q = sum(k * chi_bar[k] for k in range(1, b) if k in chi_bar)

        # P = sum chi_bar(k)
        P = sum(chi_bar[k] for k in range(1, b) if k in chi_bar)

        # coupling = sum chi_bar(k) * G(k)
        coupling = 0
        for k in range(1, b):
            if k not in chi_bar: continue
            G_k = sum((l * k // b) * psi[l] for l in range(b))
            coupling += chi_bar[k] * G_k

        signal = abs(b * F0 * Q)
        noise = abs(b * b * coupling)

        if signal > 1e-10 and abs(P) > 1e-6:
            results.append({
                'signal': signal,
                'noise': noise,
                'snr': signal / noise if noise > 1e-10 else float('inf'),
                'P': abs(P),
            })

    if not results:
        return None

    mean_snr = sum(r['snr'] for r in results) / len(results)
    med_snr = sorted(r['snr'] for r in results)[len(results)//2]

    return {
        'b': b,
        'n': len(results),
        'mean_snr': mean_snr,
        'median_snr': med_snr,
    }

print(f"{'b':>4} {'n':>4} {'mean_SNR':>10} {'med_SNR':>10} "
      f"{'SNR*logb':>10} {'SNR*sqrtb':>10}")

for b in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]:
    r = compute_snr(b)
    if r is None: continue
    snr = r['median_snr']
    print(f"{r['b']:>4} {r['n']:>4} {r['mean_snr']:>10.4f} {snr:>10.4f} "
          f"{snr*math.log(r['b']):>10.4f} "
          f"{snr*math.sqrt(r['b']):>10.4f}")
