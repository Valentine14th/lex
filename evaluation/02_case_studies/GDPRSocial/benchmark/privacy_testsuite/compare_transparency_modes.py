#!/usr/bin/env python3
import ast
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd


ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
LOG_NAME_RE = re.compile(r"^(?P<ts>\d{8}_\d{6})_(?P<scenario>.+?)_none_gdpr\.log$")


@dataclass
class LogInfo:
    path: Path
    timestamp: str
    scenario: str
    mode: str  # 'split' or 'default'


def strip_ansi(text: str) -> str:
    return ANSI_RE.sub("", text)


def detect_mode(path: Path) -> Optional[str]:
    with path.open("r", encoding="utf-8", errors="replace") as fh:
        for _ in range(40):
            line = fh.readline()
            if not line:
                break
            clean = strip_ansi(line)
            if "Multi-enforcer mode" in clean or "/app/policies/split/" in clean:
                return "split"
            if "Single enforcer mode" in clean or "/app/policies/default/" in clean:
                return "default"
    return None


def parse_log_name(path: Path) -> Optional[Tuple[str, str]]:
    m = LOG_NAME_RE.match(path.name)
    if not m:
        return None
    return m.group("ts"), m.group("scenario")


def extract_first_dict(text: str) -> Optional[dict]:
    start = text.find("{")
    if start < 0:
        return None

    depth = 0
    quote_char = None
    escaped = False
    end = None

    for idx, ch in enumerate(text[start:], start=start):
        if escaped:
            escaped = False
            continue
        if ch == "\\":
            escaped = True
            continue

        if quote_char is not None:
            if ch == quote_char:
                quote_char = None
            continue

        if ch in ("'", '"'):
            quote_char = ch
            continue

        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                end = idx + 1
                break

    if end is None:
        return None

    payload = text[start:end]
    try:
        obj = ast.literal_eval(payload)
    except Exception:
        return None

    return obj if isinstance(obj, dict) else None


def parse_transparency_counts(path: Path) -> Dict[str, Counter]:
    counts = {
        "cause": Counter(),
        "suppress": Counter(),
    }

    marker = "Received from enforcer:"
    with path.open("r", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            clean = strip_ansi(line)
            if marker not in clean:
                continue

            payload_txt = clean.split(marker, 1)[1].strip()
            payload = extract_first_dict(payload_txt)
            if not payload:
                continue

            ts = payload.get("ts")
            if ts is None:
                continue

            for kind in ("cause", "suppress"):
                events = payload.get(kind, [])
                if not isinstance(events, list):
                    continue
                for event in events:
                    if not isinstance(event, dict):
                        continue
                    name = event.get("name")
                    if not name:
                        continue
                    counts[kind][(str(name), int(ts))] += 1

    return counts


def to_dataframe(split_counter: Counter, default_counter: Counter) -> pd.DataFrame:
    columns = ["event", "ts", "split_count", "default_count", "diff_split_minus_default"]
    keys = sorted(set(split_counter.keys()) | set(default_counter.keys()), key=lambda x: (x[1], x[0]))
    rows = []
    for event, ts in keys:
        s = int(split_counter.get((event, ts), 0))
        d = int(default_counter.get((event, ts), 0))
        rows.append(
            {
                "event": event,
                "ts": ts,
                "split_count": s,
                "default_count": d,
                "diff_split_minus_default": s - d,
            }
        )
    return pd.DataFrame(rows, columns=columns)


def draw_heatmap(ax, df: pd.DataFrame, title: str):
    if df.empty:
        ax.text(0.5, 0.5, "no data", ha="center", va="center", fontsize=10)
        ax.set_title(title)
        ax.axis("off")
        return

    pivot = (
        df.pivot_table(
            index="event",
            columns="ts",
            values="diff_split_minus_default",
            aggfunc="sum",
            fill_value=0,
        )
        .sort_index()
        .reindex(sorted(df["event"].unique()), axis=0)
    )

    matrix = pivot.to_numpy(dtype=float)
    vmax = max(1.0, float(np.max(np.abs(matrix))))

    im = ax.imshow(matrix, aspect="auto", cmap="RdBu_r", vmin=-vmax, vmax=vmax)
    ax.set_title(title)
    ax.set_xlabel("Enforcer timepoint (ts)")
    ax.set_ylabel("Event")

    ax.set_xticks(np.arange(pivot.shape[1]))
    ax.set_xticklabels([str(c) for c in pivot.columns], rotation=45, ha="right", fontsize=8)
    ax.set_yticks(np.arange(pivot.shape[0]))
    ax.set_yticklabels(list(pivot.index), fontsize=8)

    cbar = plt.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
    cbar.set_label("split - default")


def ts_totals(counter: Counter) -> Dict[int, int]:
    totals: Dict[int, int] = defaultdict(int)
    for (_event, ts), cnt in counter.items():
        totals[int(ts)] += int(cnt)
    return dict(totals)


def event_totals(counter: Counter) -> Dict[str, int]:
    totals: Dict[str, int] = defaultdict(int)
    for (event, _ts), cnt in counter.items():
        totals[str(event)] += int(cnt)
    return dict(totals)


def draw_mode_overlay(ax, split_totals: Dict[int, int], default_totals: Dict[int, int], title: str):
    ts_vals = sorted(set(split_totals.keys()) | set(default_totals.keys()))
    if not ts_vals:
        ax.text(0.5, 0.5, "no data", ha="center", va="center", fontsize=10)
        ax.set_title(title)
        ax.axis("off")
        return

    split_y = [int(split_totals.get(ts, 0)) for ts in ts_vals]
    default_y = [int(default_totals.get(ts, 0)) for ts in ts_vals]

    ax.plot(ts_vals, split_y, marker="o", linewidth=1.8, label="split (multi)")
    ax.plot(ts_vals, default_y, marker="s", linewidth=1.8, label="default (single)")
    ax.set_title(title)
    ax.set_xlabel("Enforcer timepoint (ts)")
    ax.set_ylabel("Event count")
    ax.grid(True, alpha=0.25)
    ax.legend(loc="best")


def main():
    root = Path(__file__).resolve().parent
    logs_dir = root / "logs" / "multi_runs"
    out_dir = root / "output" / "transparency_diff"
    out_dir.mkdir(parents=True, exist_ok=True)

    infos: List[LogInfo] = []
    for path in sorted(logs_dir.glob("*.log")):
        parsed = parse_log_name(path)
        if not parsed:
            continue
        ts, scenario = parsed
        mode = detect_mode(path)
        if mode is None:
            continue
        infos.append(LogInfo(path=path, timestamp=ts, scenario=scenario, mode=mode))

    all_logs_df = pd.DataFrame(
        [
            {
                "log": str(info.path),
                "timestamp": info.timestamp,
                "scenario": info.scenario,
                "mode": info.mode,
            }
            for info in sorted(infos, key=lambda i: (i.timestamp, i.scenario, i.mode))
        ]
    )
    all_logs_df.to_csv(out_dir / "all_logs_mode_classification.csv", index=False)

    by_scenario: Dict[str, Dict[str, List[LogInfo]]] = defaultdict(lambda: {"split": [], "default": []})
    for info in infos:
        by_scenario[info.scenario][info.mode].append(info)

    pairs = []
    for scenario in sorted(by_scenario.keys()):
        split_logs = sorted(by_scenario[scenario]["split"], key=lambda i: i.timestamp)
        default_logs = sorted(by_scenario[scenario]["default"], key=lambda i: i.timestamp)
        if not split_logs or not default_logs:
            continue
        # Take one from each mode for this scenario: latest split and latest default.
        pairs.append((scenario, split_logs[-1], default_logs[-1]))

    pair_rows = []
    summary_rows = []
    for scenario, split_info, default_info in pairs:
        pair_rows.append(
            {
                "scenario": scenario,
                "split_log": str(split_info.path),
                "default_log": str(default_info.path),
                "split_timestamp": split_info.timestamp,
                "default_timestamp": default_info.timestamp,
            }
        )

        split_counts = parse_transparency_counts(split_info.path)
        default_counts = parse_transparency_counts(default_info.path)

        cause_df = to_dataframe(split_counts["cause"], default_counts["cause"])
        suppress_df = to_dataframe(split_counts["suppress"], default_counts["suppress"])

        base_name = scenario.replace("/", "_")
        cause_csv = out_dir / f"{base_name}_cause_diff.csv"
        suppress_csv = out_dir / f"{base_name}_suppress_diff.csv"
        cause_df.to_csv(cause_csv, index=False)
        suppress_df.to_csv(suppress_csv, index=False)

        cause_nonzero = int((cause_df["diff_split_minus_default"] != 0).sum()) if not cause_df.empty else 0
        suppress_nonzero = int((suppress_df["diff_split_minus_default"] != 0).sum()) if not suppress_df.empty else 0
        summary_rows.append(
            {
                "scenario": scenario,
                "split_log": str(split_info.path),
                "default_log": str(default_info.path),
                "cause_diff_nonzero": cause_nonzero,
                "suppress_diff_nonzero": suppress_nonzero,
            }
        )

        n_events = max(cause_df["event"].nunique() if not cause_df.empty else 1,
                       suppress_df["event"].nunique() if not suppress_df.empty else 1)
        fig_h = max(6, min(24, 2 + 0.35 * n_events))
        fig, axes = plt.subplots(2, 1, figsize=(14, fig_h), constrained_layout=True)
        draw_heatmap(axes[0], cause_df, f"{scenario}: cause diff by ts")
        draw_heatmap(axes[1], suppress_df, f"{scenario}: suppress diff by ts")

        fig_path = out_dir / f"{base_name}_diff.png"
        fig.savefig(fig_path, dpi=220)
        plt.close(fig)

        split_cause_ts = ts_totals(split_counts["cause"])
        default_cause_ts = ts_totals(default_counts["cause"])
        split_suppress_ts = ts_totals(split_counts["suppress"])
        default_suppress_ts = ts_totals(default_counts["suppress"])

        split_cause_event_totals = event_totals(split_counts["cause"])
        default_cause_event_totals = event_totals(default_counts["cause"])
        split_suppress_event_totals = event_totals(split_counts["suppress"])
        default_suppress_event_totals = event_totals(default_counts["suppress"])

        total_rows = []
        for kind, split_map, default_map in (
            ("cause", split_cause_event_totals, default_cause_event_totals),
            ("suppress", split_suppress_event_totals, default_suppress_event_totals),
        ):
            event_names = sorted(set(split_map.keys()) | set(default_map.keys()))
            for event_name in event_names:
                split_n = int(split_map.get(event_name, 0))
                default_n = int(default_map.get(event_name, 0))
                total_rows.append(
                    {
                        "kind": kind,
                        "event": event_name,
                        "split_total": split_n,
                        "default_total": default_n,
                        "diff_split_minus_default": split_n - default_n,
                        "match": split_n == default_n,
                    }
                )
        totals_df = pd.DataFrame(
            total_rows,
            columns=[
                "kind",
                "event",
                "split_total",
                "default_total",
                "diff_split_minus_default",
                "match",
            ],
        )
        totals_df.to_csv(out_dir / f"{base_name}_event_type_totals_match.csv", index=False)

        cause_match = True
        suppress_match = True
        if not totals_df.empty:
            cause_view = totals_df[totals_df["kind"] == "cause"]
            suppress_view = totals_df[totals_df["kind"] == "suppress"]
            if not cause_view.empty:
                cause_match = bool(cause_view["match"].all())
            if not suppress_view.empty:
                suppress_match = bool(suppress_view["match"].all())

        summary_rows[-1]["cause_event_type_totals_match"] = cause_match
        summary_rows[-1]["suppress_event_type_totals_match"] = suppress_match
        summary_rows[-1]["all_event_type_totals_match"] = cause_match and suppress_match

        ts_values = sorted(
            set(split_cause_ts.keys())
            | set(default_cause_ts.keys())
            | set(split_suppress_ts.keys())
            | set(default_suppress_ts.keys())
        )
        overlay_rows = []
        for ts in ts_values:
            overlay_rows.append(
                {
                    "ts": ts,
                    "split_cause": int(split_cause_ts.get(ts, 0)),
                    "default_cause": int(default_cause_ts.get(ts, 0)),
                    "split_suppress": int(split_suppress_ts.get(ts, 0)),
                    "default_suppress": int(default_suppress_ts.get(ts, 0)),
                }
            )
        pd.DataFrame(overlay_rows).to_csv(out_dir / f"{base_name}_mode_ts_totals.csv", index=False)

        overlay_fig, overlay_axes = plt.subplots(2, 1, figsize=(14, 8), constrained_layout=True)
        draw_mode_overlay(
            overlay_axes[0],
            split_cause_ts,
            default_cause_ts,
            f"{scenario}: caused events per ts (split vs default)",
        )
        draw_mode_overlay(
            overlay_axes[1],
            split_suppress_ts,
            default_suppress_ts,
            f"{scenario}: suppressed events per ts (split vs default)",
        )
        overlay_fig.savefig(out_dir / f"{base_name}_mode_overlay.png", dpi=220)
        plt.close(overlay_fig)

    pair_map = pd.DataFrame(pair_rows)
    pair_map.to_csv(out_dir / "scenario_mode_pairs.csv", index=False)

    pd.DataFrame(summary_rows).to_csv(out_dir / "scenario_diff_summary.csv", index=False)

    print(f"Wrote outputs to: {out_dir}")
    print(f"Scenarios compared: {len(pairs)}")


if __name__ == "__main__":
    main()
