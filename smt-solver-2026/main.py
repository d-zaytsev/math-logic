import sys
from traceback import print_exc

from arrays import array_to_euf_tests
from congruence import CongruenceSolver_tests
from dpll_t import DPLL_T_Solver_tests


def main():
    total_points = 0
    tests = {
        CongruenceSolver_tests: 6,
        DPLL_T_Solver_tests: 4,
        array_to_euf_tests: 5,
    }

    passed = []
    failed = []

    for test, points in tests.items():
        try:
            test()
            print(f"Gained +{points}")
            total_points += points
            passed.append((test.__name__, points))
        except Exception:  # noqa: BLE001
            print("Gained no points because of error:")
            print_exc(None, sys.stdout, False)
            failed.append((test.__name__, points))
    print(f"Total points for this homework: {total_points}")

    from utils import github_autograder_report

    github_autograder_report(passed, failed)


if __name__ == "__main__":
    main()
