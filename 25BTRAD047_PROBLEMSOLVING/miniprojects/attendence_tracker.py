
"""
Attendance Tracker using Lists and Dictionaries

Data structure:
attendance = {
    "Student Name": ["P", "A", "P", ...]
}

DICT: Maps each student to their attendance record.
LIST: Stores attendance for each class day.
P = Present
A = Absent
"""

VALID = ("P", "A")


def add_student(attendance, name):
    name = name.strip()

    if not name:
        return False, "Name cannot be empty."

    if name in attendance:
        return False, f"'{name}' already exists."

    attendance[name] = []
    return True, f"Added '{name}'."


def mark_day(attendance, statuses):
    """
    Record attendance for one new class day.
    statuses = {name: 'P'/'A'}
    Unlisted students are marked absent.
    """

    # Validate all entries before modifying attendance
    for name, status in statuses.items():
        if name not in attendance:
            return False, f"'{name}' not found."

        if not isinstance(status, str) or status.upper() not in VALID:
            return False, f"Invalid status '{status}' for {name}. Use P or A."

    # Record attendance
    for name in attendance:
        status = statuses.get(name, "A")
        attendance[name].append(status.upper())

    return True, "Attendance recorded."


def update_attendance(attendance, name, day, status):
    """Correct an earlier attendance entry. Day is 1-based."""

    if name not in attendance:
        return False, f"'{name}' not found."

    if not isinstance(status, str) or status.upper() not in VALID:
        return False, "Status must be P or A."

    if not isinstance(day, int) or not 1 <= day <= len(attendance[name]):
        return False, f"Day {day} has no record for {name}."

    attendance[name][day - 1] = status.upper()

    return True, f"Updated {name}, day {day} -> {status.upper()}."


def percentage(records):
    if not records:
        return 0.0

    return records.count("P") / len(records) * 100


def below_threshold(attendance, threshold=75):
    return {
        name: round(percentage(records), 1)
        for name, records in attendance.items()
        if records and percentage(records) < threshold
    }


def display(attendance, threshold=75):
    if not attendance:
        print("(no students)")
        return

    days = max(len(records) for records in attendance.values())

    header = f"{'Student':<12}" + "".join(
        f"D{day:<3}" for day in range(1, days + 1)
    )

    print(header + f"{'Present':>9}{' %':>8} Status")
    print("-" * (len(header) + 28))

    for name, records in attendance.items():
        pct = percentage(records)

        row = f"{name:<12}" + "".join(
            f"{status:<4}" for status in records
        )

        row += " " * (4 * (days - len(records)))

        flag = "SHORTAGE" if records and pct < threshold else "OK"

        print(
            f"{row}{records.count('P'):>6}/{len(records):<2}"
            f"{pct:>7.1f}% {flag}"
        )


def run_tests():
    attendance = {}

    for name in ("Asha", "Ravi", "Meena"):
        assert add_student(attendance, name)[0]

    assert not add_student(attendance, "Asha")[0]
    assert not add_student(attendance, " ")[0]

    # Scenario 1: Normal week
    mark_day(attendance, {
        "Asha": "P", "Ravi": "P", "Meena": "A"
    })

    mark_day(attendance, {
        "Asha": "P", "Ravi": "A", "Meena": "A"
    })

    mark_day(attendance, {
        "Asha": "P", "Ravi": "P", "Meena": "A"
    })

    mark_day(attendance, {
        "Asha": "P", "Ravi": "P"
    })

    assert percentage(attendance["Asha"]) == 100
    assert percentage(attendance["Ravi"]) == 75
    assert percentage(attendance["Meena"]) == 0

    assert below_threshold(attendance, 75) == {
        "Meena": 0.0
    }

    assert set(below_threshold(attendance, 80)) == {
        "Ravi", "Meena"
    }

    # Scenario 2: Update attendance
    assert update_attendance(attendance, "Ravi", 2, "p")[0]
    assert percentage(attendance["Ravi"]) == 100

    assert not update_attendance(attendance, "Ravi", 9, "P")[0]
    assert not update_attendance(attendance, "Ravi", 1, "X")[0]
    assert not update_attendance(attendance, "Zed", 1, "P")[0]

    # Scenario 3: Invalid input leaves data unchanged
    before = {
        key: value[:]
        for key, value in attendance.items()
    }

    assert not mark_day(attendance, {"Asha": "Q"})[0]
    assert not mark_day(attendance, {"Ghost": "P"})[0]

    assert attendance == before

    # Scenario 4: Late student
    add_student(attendance, "Late")

    assert percentage(attendance["Late"]) == 0
    assert "Late" not in below_threshold(attendance)

    print("All attendance tests passed.")


def main():
    run_tests()

    attendance = {}

    for name in ("Asha", "Ravi", "Meena", "Kabir"):
        add_student(attendance, name)

    # Sample weekly attendance
    week = [
        {"Asha": "P", "Ravi": "P", "Meena": "P", "Kabir": "A"},
        {"Asha": "P", "Ravi": "A", "Meena": "P", "Kabir": "A"},
        {"Asha": "P", "Ravi": "P", "Meena": "A", "Kabir": "A"},
        {"Asha": "A", "Ravi": "P", "Meena": "P", "Kabir": "P"},
    ]

    for day in week:
        mark_day(attendance, day)

    print("\n=== SAMPLE CLASS ===")
    display(attendance)

    low = below_threshold(attendance, 75)

    print(
        "\nBelow 75%:",
        ", ".join(
            f"{name} ({percentage_value}%)"
            for name, percentage_value in low.items()
        ) or "none"
    )

    menu = (
        "\n1. Add student"
        "\n2. Mark today's attendance"
        "\n3. Update a record"
        "\n4. Display attendance"
        "\n5. Shortage list"
        "\n6. Exit"
    )

    while True:
        print(menu)
        choice = input("Choice: ").strip()

        if choice == "1":
            name = input("Name: ")
            print(add_student(attendance, name)[1])

        elif choice == "2":
            statuses = {
                name: input(f"{name} (P/A): ").strip() or "A"
                for name in attendance
            }

            print(mark_day(attendance, statuses)[1])

        elif choice == "3":
            try:
                name = input("Name: ").strip()
                day = int(input("Day number: "))
                status = input("New status (P/A): ").strip()

                print(
                    update_attendance(
                        attendance, name, day, status
                    )[1]
                )

            except ValueError:
                print("Day must be a number.")

        elif choice == "4":
            display(attendance)

        elif choice == "5":
            try:
                threshold = float(input("Threshold %: "))

                if not 0 <= threshold <= 100:
                    print("Threshold must be between 0 and 100.")
                    continue

                print(
                    below_threshold(attendance, threshold)
                    or "No one is below the threshold."
                )

            except ValueError:
                print("Enter a valid number.")

        elif choice == "6":
            print("Exiting Attendance Tracker. Goodbye!")
            break

        else:
            print("Invalid choice. Please try again.")


if __name__ == "__main__":
    main()
