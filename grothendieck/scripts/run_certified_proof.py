#!/usr/bin/env python3
"""
CLI entry point for the certified proof pipeline.

Usage:
    uv run python scripts/run_certified_proof.py
    uv run python scripts/run_certified_proof.py --eta 0.01 --polynomial h3 --r 0.92
    uv run python scripts/run_certified_proof.py --output outputs/certificate.json
"""

import argparse
import os


def main():
    parser = argparse.ArgumentParser(
        description="Run certified proof that K_G > 2/pi + delta"
    )
    parser.add_argument("--eta", type=float, default=0.01,
                        help="Perturbation parameter (default: 0.01)")
    parser.add_argument("--polynomial", type=str, default="h3",
                        choices=["h3", "h5"],
                        help="Hermite polynomial for P and Q (default: h3)")
    parser.add_argument("--r", type=float, default=0.92,
                        help="Disk radius (default: 0.92)")
    parser.add_argument("--alpha", type=float, default=1.10,
                        help="Ratio rho/gamma_0 (default: 1.02)")
    parser.add_argument("--prec", type=int, default=128,
                        help="Arb precision in bits (default: 128)")
    parser.add_argument("--K-max", type=int, default=250,
                        help="Max Taylor series terms (default: 250)")
    parser.add_argument("--b-series", type=str, default=None,
                        help="Path to cached b_k JSON (skips coefficient computation)")
    parser.add_argument("--output", type=str, default=None,
                        help="Path to save certificate JSON")
    parser.add_argument("--quiet", action="store_true",
                        help="Suppress verbose output")

    args = parser.parse_args()

    # Select arb polynomial
    from grothendieck.proof.certified.bk_rigor import h3_arb, h5_arb

    poly_arb_map = {"h3": h3_arb, "h5": h5_arb}
    P_arb = poly_arb_map[args.polynomial]
    Q_arb = poly_arb_map[args.polynomial]

    # Create output directory if needed
    if args.output:
        os.makedirs(os.path.dirname(args.output) or ".", exist_ok=True)

    # Run the proof
    from grothendieck.proof.certified.run_proof import run_certified_proof

    cert = run_certified_proof(
        eta=args.eta,
        P_arb=P_arb,
        Q_arb=Q_arb,
        P_name=args.polynomial,
        Q_name=args.polynomial,
        r=args.r,
        alpha=args.alpha,
        prec=args.prec,
        K_max=args.K_max,
        b_series_path=args.b_series,
        p_override=1e-30,
        output_path=args.output,
        verbose=not args.quiet,
    )

    # Exit code based on proof result
    if cert.all_checks_passed:
        print("\nPROOF SUCCEEDED: All checks passed.")
        return 0
    else:
        print("\nPROOF INCOMPLETE: Some checks failed.")
        return 1


if __name__ == "__main__":
    exit(main())
