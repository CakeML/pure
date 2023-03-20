#!/usr/bin/python3
import argparse
import configparser
import os
import subprocess
import sys
import time

import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import pandas
import parse

# Parsing arguments / config

def parseArgs():
    parser = argparse.ArgumentParser(
        prog="benchmark.py",
        description="PureCake benchmarking. Configure using `bench.config`.")
    parser.add_argument("--mode", choices=["collect", "plot", "compile"], default="collect",
                        help="Mode of operation (default: %(default)s).")
    parser.add_argument("--filestem", default="data",
                        help="file stem to use for data/PDF output (default: %(default)s)")
    return parser.parse_args()


def parseConfig():
    cfg = configparser.ConfigParser()
    cfg.optionxform = lambda x: x
    cfg.read("bench.config")
    return cfg


# Benchmarking (--mode collect)

def compile(program, flags, heap):
    pureopt = "PUREOPT"
    cml_heap_size = "CML_HEAP_SIZE"
    debug = "DEBUG"
    env = os.environ.copy()
    env[pureopt] = flags
    env[cml_heap_size] = heap
    env[debug] = str(1)
    cmd = ["make", "-C", "../", program + ".exe"]
    print(
        f"Compiling: {pureopt}='{env[pureopt]}' {cml_heap_size}='{env[cml_heap_size]}' {debug}='{env[debug]}' {' '.join(cmd)}")
    complete = subprocess.run(["make", "-C", "../", program + ".exe"],
                              env=env, capture_output=True)
    if complete.returncode != 0:
        print("Failed to compile program.", file=sys.stderr)
        print(complete.stderr.decode(), file=sys.stderr)
        sys.exit(1)


def runCommand(command):
    start = time.time()
    complete = subprocess.run(command, capture_output=True)
    end = time.time()
    if complete.returncode == 0:
        lastLine = complete.stderr.decode().splitlines()[-1]
        parsed = parse.parse("Total allocated heap data: {allocated:d} bytes", lastLine)
        return (True, end - start, parsed.named['allocated'])
    else:
        print("Program exited with non-zero code: " +
              str(complete.returncode), file=sys.stderr)
        print(complete.stderr.decode(), file=sys.stderr)
        return (False, 0, 0)


def benchmark(program, inp, iterations):
    results = []
    executable = "../out/" + program + ".exe"
    print(f"Timing ({iterations} iterations): {executable} {inp}")
    for i in range(0, iterations):
        (ok, duration, allocated) = runCommand([executable, inp])
        if ok:
            results.append((duration, allocated))
        print("." if ok else "#", end="", flush=True)
    print(" Done.\n")
    return results


def recordRuns(results, filestem):
    with open(filestem + ".csv", 'w') as f:
        f.write(f"Benchmark,Flags,Time,Allocated\n")
        for program, flagResults in results.items():
            for flagGroup, data in flagResults.items():
                for t, bs in data:
                    f.write(f"{program},{flagGroup},{round(t,1)},{bs}\n")


def collectData():
    cfg = parseConfig()
    iters = cfg.getint("settings", "iterations")
    heap = cfg.get("settings", "heap")
    print(f"\033[1mIterations: {iters}, heap size: {heap} MB\033[0m\n")

    results = {}
    for program in cfg["programs"]:
        inp = cfg.get("programs", program)
        results[program] = {}
        for flagGroup, flags in cfg["flags"].items():
            print(
                f"\033[1mBenchmarking {program} (input: {inp}, flag group: {flagGroup})\033[0m")
            compile(program, "-final_gc " + flags, heap)
            results[program][flagGroup] = benchmark(program, inp, iters)
    return results


# Compile all programs (--mode compile)

def compileAll():
    cfg = parseConfig()
    heap = cfg.get("settings", "heap")
    print(f"\033[1mCompiling all programs (heap size: {heap} MB)\033[0m\n")
    for program in cfg["programs"]:
        for flagGroup, flags in cfg["flags"].items():
            compile(program, flags, heap)


# Plot graph (--mode plot)

def transformData(filestem):
    df = pandas.read_csv(filestem + ".csv")
    df = df.groupby(["Benchmark", "Flags"], sort=False).mean()

    # Extract + delete first rows of each group
    firstRows = df.reset_index(level="Flags", drop=True).groupby(
        "Benchmark", sort=False).first()
    df = df.reset_index(level="Flags").groupby("Benchmark", sort=False, group_keys=False).apply(
        lambda x: x.iloc[1:]).set_index(["Flags"], append=True)

    # Transform data
    df = df.divide(firstRows).apply(np.log2)
    return df


def plotData(df):
    df = df.reset_index().pivot_table(index="Benchmark", columns="Flags", sort=False)

    plt.tight_layout()
    fig, axes = plt.subplots(nrows=2, ncols=1)
    df["Time"].plot(ax=axes[0], kind="bar", rot=0,
                    ylabel="log2(speedup)", legend=False)
    df["Allocated"].plot(ax=axes[1], kind="bar", rot=0,
                  ylabel="log2(allocation reduction)", sharex=True, legend=False)
    axes[0].legend(title="Optimisations", ncol=4,
                   loc="upper center", bbox_to_anchor=(0.5, 1.35))

    for ax in fig.axes:
        ax.axhline(y=0, color="black", linewidth=0.1)
        ax.yaxis.set_major_formatter(
            matplotlib.ticker.FormatStrFormatter('%.1f'))
        ax.tick_params(labelsize="small")

    return fig


# Main function

if __name__ == "__main__":
    args = parseArgs()
    if args.mode == "collect":
        data = collectData()
        recordRuns(data, args.filestem)
    elif args.mode == "compile":
        compileAll()
    elif args.mode == "plot":
        df = transformData(args.filestem)
        fig = plotData(df)
        fig.savefig(args.filestem + ".pdf")
    else:
        print("ERROR: unexpected mode")

