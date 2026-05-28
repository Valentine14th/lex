#!/usr/bin/env bash
#
# run_benchmark.sh — Prepare databases then run the full performance benchmark.
#
# Usage:
#   ./benchmark/privacy_testsuite/run_benchmark.sh <policy> [<enfguard_exe>] [--instrlib <path>] [--formula <path>] [--sig <path>] [--output-dir <path>] [--run-label <name>]
#
# For enforced policies supply the enfguard executable:
#   ./benchmark/privacy_testsuite/run_benchmark.sh gdpr /opt/whyenf/enfguard
#
# To run with a specific instrlib version:
#   ./benchmark/privacy_testsuite/run_benchmark.sh gdpr /opt/whyenf/enfguard --instrlib /path/to/instrlib
#
# To override formula(s) and/or signature file(s) (comma-separated for multiple):
#   ./benchmark/privacy_testsuite/run_benchmark.sh gdpr /opt/whyenf/enfguard --formula policies/a.mfotl,policies/b.mfotl --sig policies/a.sig,policies/b.sig
#
# Or pass a folder to --formula; all .mfotl files are used and matching .sig files auto-detected:
#   ./benchmark/privacy_testsuite/run_benchmark.sh gdpr /opt/whyenf/enfguard --formula policies/
#
# To specify an explicit output directory (useful in Docker with bind mounts):
#   ./benchmark/privacy_testsuite/run_benchmark.sh gdpr /opt/whyenf/enfguard --output-dir /app/output
#
# For the un-instrumented baseline no enforcer argument is required:
#   ./benchmark/privacy_testsuite/run_benchmark.sh baseline
#
set -euo pipefail
cd "$(dirname "$0")/../.."   # → miniTwitter_gdpr/

POLICY="${1:?Usage: $0 <policy> [<enfguard_exe>] [--instrlib <path>] [--formula <path>] [--sig <path>] [--output-dir <path>] [--run-label <name>]}"

# EXE is only required for enforced policies.
if [[ "${POLICY}" == "baseline" ]]; then
    EXE=""
    shift
else
    EXE="${2:?Enforced policy '${POLICY}' requires an <enfguard_exe> argument.}"
    shift 2
fi

# Optional arguments.
INSTRLIB_ARG=""
FORMULA_ARG=""
SIG_ARG=""
FORMULA_DIR=""
OUTPUT_DIR_OVERRIDE=""
RUN_LABEL=""
while [[ $# -gt 0 ]]; do
    case "$1" in
        --instrlib)
            INSTRLIB_ARG="-i ${2:?--instrlib requires a path argument}"
            shift 2
            ;;
        --formula)
            FORMULA_VAL="${2:?--formula requires a path or directory}"
            FORMULA_VAL="${FORMULA_VAL%/}"   # strip trailing slash
            if [[ -d "$FORMULA_VAL" ]]; then
                FORMULA_DIR="$FORMULA_VAL"
                mapfile -t _mfotl_files < <(ls "$FORMULA_VAL"/*.mfotl 2>/dev/null | sort)
                if [[ ${#_mfotl_files[@]} -eq 0 ]]; then
                    echo "--formula: no .mfotl files found in $FORMULA_VAL" >&2; exit 1
                fi
                FORMULA_LIST=$(IFS=,; echo "${_mfotl_files[*]}")
                FORMULA_ARG="-formula ${FORMULA_LIST}"
            else
                FORMULA_ARG="-formula $FORMULA_VAL"
            fi
            shift 2
            ;;
        --sig)
            SIG_ARG="-sig ${2%/}"
            shift 2
            ;;
        --output-dir)
            OUTPUT_DIR_OVERRIDE="${2:?--output-dir requires a path}"
            shift 2
            ;;
        --run-label)
            RUN_LABEL="${2:?--run-label requires a value}"
            shift 2
            ;;
        *)
            echo "Unknown argument: $1" >&2
            exit 1
            ;;
    esac
done

# If --formula was a directory and --sig was not given, auto-detect .sig files from same dir.
if [[ -n "$FORMULA_DIR" && -z "$SIG_ARG" ]]; then
    mapfile -t _sig_files < <(ls "${FORMULA_DIR}"/*.sig 2>/dev/null | sort)
    if [[ ${#_sig_files[@]} -gt 0 ]]; then
        SIG_LIST=$(IFS=,; echo "${_sig_files[*]}")
        SIG_ARG="-sig ${SIG_LIST}"
    fi
fi

OUTPUT_ROOT="$(realpath "${OUTPUT_DIR_OVERRIDE:-output}")"
if [[ -n "${RUN_LABEL}" ]]; then
    OUTPUT_DIR="${OUTPUT_ROOT}/${RUN_LABEL}"
else
    OUTPUT_DIR="${OUTPUT_ROOT}"
fi
mkdir -p "${OUTPUT_DIR}"
echo "  Output directory: ${OUTPUT_DIR}"

echo "══════════════════════════════════════════════════════════"
echo "  Step 1 – Preparing database snapshots"
echo "══════════════════════════════════════════════════════════"
python3 benchmark/privacy_testsuite/prepare_databases.py

echo ""
echo "══════════════════════════════════════════════════════════"
echo "  Step 2 – Running benchmark  (policy=${POLICY})"
echo "══════════════════════════════════════════════════════════"
echo "  Enforcer:  ${EXE:-<none (baseline)>}"
if [[ -n "${INSTRLIB_ARG}" ]]; then
    _instrlib_path="${INSTRLIB_ARG#-i }"
    echo "  Instrlib:  ${_instrlib_path}"
    if [[ ! -e "${_instrlib_path}" ]]; then
        echo "  ERROR: instrlib path does not exist inside the container: ${_instrlib_path}" >&2
        exit 1
    fi
else
    echo "  Instrlib:  <default (baked into image)>"
fi
if [[ -n "${FORMULA_ARG}" ]]; then
    echo "  Formula(s):"
    IFS=',' read -ra _flist <<< "${FORMULA_ARG#-formula }"
    for _f in "${_flist[@]}"; do echo "             $_f"; done
else
    echo "  Formula:   <default>"
fi
if [[ -n "${SIG_ARG}" ]]; then
    echo "  Sig(s):    ${SIG_ARG#-sig }"
fi
echo "══════════════════════════════════════════════════════════"
python3 benchmark/privacy_testsuite/privacy_test.py minitwitter \
    -f "${OUTPUT_DIR}" \
    -p "${POLICY}" \
    -e "${EXE}" \
    ${INSTRLIB_ARG} \
    ${FORMULA_ARG} \
    ${SIG_ARG}

echo ""
echo "══════════════════════════════════════════════════════════"
echo "  Done — results in ${OUTPUT_DIR}/"
echo "══════════════════════════════════════════════════════════"
