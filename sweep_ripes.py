#!/usr/bin/env python3

from pathlib import Path
import csv
import re
import subprocess
import sys
import time

RIPES = (
    "/mnt/c/Users/user/Desktop/"
    "Ripes-v2.2.6-106-g5b8a616-win-x86_64/Ripes.exe"
)

ELF = Path("solver_cli.elf")
BIN = Path("solver_cli.bin")
STATES_FILE = Path("depth11_states.txt")

WORK_BIN = Path("sweep_state.bin")
RIPES_OUT = Path("sweep_iret.txt")
CSV_FILE = Path("depth11_iret.csv")

EXPECTED = 2644
LIMIT = 50_000_000


def winpath(path):
    return subprocess.check_output(
        ["wslpath", "-w", str(path.resolve())],
        text=True
    ).strip()


def get_input_offset():
    out = subprocess.check_output(
        ["riscv64-unknown-elf-nm", "-n", str(ELF)],
        text=True
    )

    for line in out.splitlines():
        parts = line.split()
        if len(parts) >= 3 and parts[-1] == "input_state":
            return int(parts[0], 16)

    raise RuntimeError("input_state symbol not found")


def load_states():
    states = []

    for line in STATES_FILE.read_text().splitlines():
        if not line.strip():
            continue

        state, rank = line.split()

        if len(state) != 14:
            raise RuntimeError(f"bad state: {state}")

        states.append((state, int(rank)))

    if len(states) != EXPECTED:
        raise RuntimeError(
            f"expected {EXPECTED} states, got {len(states)}"
        )

    return states


def parse_iret():
    text = RIPES_OUT.read_text(errors="replace")

    m = re.search(
        r"===== instructions retired\s+(\d+)",
        text
    )

    if not m:
        raise RuntimeError(
            "could not parse Ripes output:\n" + text
        )

    return int(m.group(1))


def main():
    states = load_states()
    offset = get_input_offset()

    base = bytearray(BIN.read_bytes())

    print(f"input_state offset: 0x{offset:x}")
    print(
        "binary input before patch:",
        repr(bytes(base[offset:offset + 15]))
    )

    work_win = winpath(WORK_BIN)
    out_win = winpath(RIPES_OUT)

    previous = {}

    if CSV_FILE.exists():
        with CSV_FILE.open(newline="") as f:
            reader = csv.DictReader(f)
            for row in reader:
                previous[row["state"]] = {
                    "rank": int(row["rank"]),
                    "iret": int(row["iret"]),
                }

        print(f"resuming with {len(previous)} completed states")

    new_csv = not CSV_FILE.exists()

    with CSV_FILE.open("a", newline="") as fp:
        writer = csv.writer(fp)

        if new_csv:
            writer.writerow(
                ["index", "rank", "state", "iret", "seconds"]
            )
            fp.flush()

        for index, (state, rank) in enumerate(states, 1):

            if state in previous:
                continue

            patched = bytearray(base)

            # Replace only the 14 state characters.
            # Existing NUL byte remains unchanged.
            patched[offset:offset + 14] = state.encode("ascii")

            WORK_BIN.write_bytes(patched)

            if RIPES_OUT.exists():
                RIPES_OUT.unlink()

            start = time.time()

            result = subprocess.run([
                RIPES,
                "--mode", "cli",
                "--src", work_win,
                "-t", "bin",
                "--proc", "RV32_ISS",
                "--iret",
                "--runinfo",
                "--output", out_win,
                "--timeout", "60000",
            ])

            seconds = time.time() - start

            if result.returncode != 0:
                raise RuntimeError(
                    f"Ripes failed at state {state}, rank {rank}"
                )

            iret = parse_iret()

            writer.writerow([
                index,
                rank,
                state,
                iret,
                f"{seconds:.6f}"
            ])
            fp.flush()

            previous[state] = {
                "rank": rank,
                "iret": iret,
            }

            current_max_state = max(
                previous,
                key=lambda s: previous[s]["iret"]
            )
            current_max = previous[current_max_state]["iret"]

            if index == 1 or index % 25 == 0:
                print(
                    f"[{index:4d}/{EXPECTED}] "
                    f"{state} "
                    f"iret={iret:,} "
                    f"max={current_max:,}"
                )

            if iret > LIMIT:
                print()
                print("50M GATE FAILED")
                print(f"state = {state}")
                print(f"rank  = {rank}")
                print(f"iret  = {iret:,}")
                return 2

    if len(previous) != EXPECTED:
        print(
            f"completed {len(previous)} / {EXPECTED}"
        )
        return 1

    min_state = min(
        previous,
        key=lambda s: previous[s]["iret"]
    )
    max_state = max(
        previous,
        key=lambda s: previous[s]["iret"]
    )

    values = [x["iret"] for x in previous.values()]

    print()
    print("===== FINAL DISTANCE-11 RV32_ISS SWEEP =====")
    print(f"states:        {len(values)}")

    print(
        f"minimum iret:  {previous[min_state]['iret']:,}"
    )
    print(f"minimum state: {min_state}")
    print(
        f"minimum rank:  {previous[min_state]['rank']}"
    )

    print(
        f"maximum iret:  {previous[max_state]['iret']:,}"
    )
    print(f"maximum state: {max_state}")
    print(
        f"maximum rank:  {previous[max_state]['rank']}"
    )

    print(
        f"average iret:  {sum(values) / len(values):,.2f}"
    )

    required = previous["21345671111111"]

    print(
        "required state: "
        f"{required['iret']:,}"
    )

    print(
        "50M gate:      ",
        "PASS" if previous[max_state]["iret"] <= LIMIT
        else "FAIL"
    )

    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print(
            "\nInterrupted; completed results remain "
            "in depth11_iret.csv."
        )
        sys.exit(130)
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)