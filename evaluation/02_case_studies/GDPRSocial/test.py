def total_time_in_log(fn: str) -> float:
    total_time = 0.0
    with open(fn, 'r') as f:
        for line in f:
            if "Time spent in log" in line:
                try:
                    total_time += float(line.split("Time spent in log:")[1].strip().replace("ms", "")) / 1000.0
                except (IndexError, ValueError) as e:
                    print(f"Error parsing line: {line}. Error: {e}")
    return total_time

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="Extract total time spent in log from a log file.")
    parser.add_argument("log_file", type=str, help="Path to the log file")
    args = parser.parse_args()

    total_time = total_time_in_log(args.log_file)
    print(f"Total time spent in log: {total_time} seconds")