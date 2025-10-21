#!./python

import sys
import pandas as pd

def parse_log(filepath):
    columns = ["SeqHost", "Host", "Starttime", "JobRuntime", "Send", "Receive", "Exitval", "Signal", "Command"]
    data = []

    with open(filepath, "r") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("Seq"):
                continue
            parts = line.split("\t")
            if len(parts) < 9:
                parts = line.split()

            # Clean "SeqHost" field (e.g., "6:" → "6")
            parts[0] = parts[0].replace(":", "")
            data.append(parts)

    df = pd.DataFrame(data, columns=columns)

    # Keep only desired columns
    df = df[["SeqHost", "JobRuntime", "Exitval", "Signal", "Command"]]

    # Convert SeqHost to integer for sorting
    df["SeqHost"] = df["SeqHost"].astype(int)

    # Sort numerically by SeqHost
    df = df.sort_values(by="SeqHost").reset_index(drop=True)
    return df

def main():
    if len(sys.argv) < 2:
        print("Usage: python parse_log.py <log_file>")
        sys.exit(1)

    filepath = sys.argv[1]
    df = parse_log(filepath)

    # Print nicely formatted output
    print(df.to_string(index=False))

    # Uncomment to save results
    #df.to_csv("parsed_log.csv", index=False)
    # df.to_excel("parsed_log.xlsx", index=False)

if __name__ == "__main__":
    main()
