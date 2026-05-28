#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."   # → GDPRSocial/

INSTRLIB="/app/instrlib"
EXE="/opt/whyenf/enfguard"

SPLITS=(
    split
    default
    split_3_19
    #split_10_8
    #split_nomerge_50
    #split_single
)

TOTAL=${#SPLITS[@]}
IDX=0
RUN_TS=$(date +%Y%m%d_%H%M%S)
HOST_RUN_LOG_DIR="output/docker_runs/${RUN_TS}"
mkdir -p "${HOST_RUN_LOG_DIR}"
FAILED_SPLITS=()

# Do not build by default; reuse existing image for all splits.
# Set BUILD_ONCE=1 to force a one-time build before running.
BUILD_ONCE="${BUILD_ONCE:-0}"
if [[ "${BUILD_ONCE}" == "1" ]]; then
    echo "Building benchmark image once..."
    docker compose build benchmark
fi

ACTIVE_RUN_PID=""
cleanup_on_signal() {
    echo ""
    echo "Stopping benchmark runner..."
    if [[ -n "${ACTIVE_RUN_PID}" ]] && kill -0 "${ACTIVE_RUN_PID}" 2>/dev/null; then
        kill -TERM "${ACTIVE_RUN_PID}" 2>/dev/null || true
        wait "${ACTIVE_RUN_PID}" 2>/dev/null || true
    fi
    exit 130
}
trap cleanup_on_signal INT TERM

for DIR in "${SPLITS[@]}"; do
    IDX=$(( IDX + 1 ))
    echo "══════════════════════════════════════════════════════════"
    echo "  Run ${IDX}/${TOTAL}: policies/${DIR}"
    echo "══════════════════════════════════════════════════════════"
    echo "  Host run log: ${HOST_RUN_LOG_DIR}/${IDX}_${DIR}.log"

    docker compose run --rm benchmark \
        gdpr "${EXE}" \
        --instrlib "${INSTRLIB}" \
        --formula "/app/policies/${DIR}" \
        --run-label "${DIR}" \
        --output-dir /app/output \
        > >(tee "${HOST_RUN_LOG_DIR}/${IDX}_${DIR}.log") 2>&1 &

    ACTIVE_RUN_PID=$!
    if ! wait "${ACTIVE_RUN_PID}"; then
        echo "  Split failed: ${DIR}"
        FAILED_SPLITS+=("${DIR}")
    else
        echo "  Split succeeded: ${DIR}"
    fi
    ACTIVE_RUN_PID=""

    echo ""
done

echo "All done. Results are in ${HOST_RUN_LOG_DIR}/"

if [[ ${#FAILED_SPLITS[@]} -gt 0 ]]; then
    echo "Failed splits (${#FAILED_SPLITS[@]}): ${FAILED_SPLITS[*]}"
    exit 1
fi

echo "All splits completed successfully."
