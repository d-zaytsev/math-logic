def github_autograder_report(passed_tests, failed_tests):
    report_entries = []

    for name, score in passed_tests:
        report_entries.extend(_github_autograder_report_entry(name, score, "pass"))

    for name, score in failed_tests:
        report_entries.extend(_github_autograder_report_entry(name, score, "fail"))

    max_score = sum(score for _, score in passed_tests) + sum(
        score for _, score in failed_tests
    )

    results = {
        "version": 1,
        "status": "pass",
        "tests": report_entries,
        "max_score": max_score,
    }

    import json

    with open("results.json", "w") as f:
        json.dump(results, f)


def _github_autograder_report_entry(name, score, status):
    entry = {
        "name": name,
        "status": status,
        "message": None,
        "line_no": None,
        "execution_time": "0ms",
        "score": 1 if status == "pass" else 0,
    }
    return [entry] * score
