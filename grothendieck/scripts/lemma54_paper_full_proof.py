"""
Run the full certified proof pipeline at r=23/25, eta=1/100 — the parameters
used by ProofRefinement/Lemma54/Candidates/V0.lean. Reports the final
certificate (gamma, c = 2/pi · gamma, etc.) and the intermediate Cr.

Long-running (10-30 min depending on machine).
"""

from grothendieck.proof.certified.run_proof import run_certified_proof


def main():
    cert = run_certified_proof(
        eta=0.01,
        r=23 / 25,
        prec=128,
        verbose=True,
    )
    print()
    print("=" * 60)
    print("FINAL CERTIFICATE")
    print("=" * 60)
    print(cert)


if __name__ == "__main__":
    main()
