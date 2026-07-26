#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "${SCRIPT_DIR}/.."   # → GDPRSocial/

# Ignore any caller-provided compose file override; this runner should use
# the repo-local docker-compose.yml from the project root above.
unset COMPOSE_FILE

INSTRLIB="/app/instrlib"
EXE="/opt/whyenf/enfguard"

# Snapshot tag used by prepare_databases.py: p<policy>_u<U>_n<N>_c<CONSENT>
SNAPSHOT_USERS="${SNAPSHOT_USERS:-1}"
SNAPSHOT_TWEETS="${SNAPSHOT_TWEETS:-100}"
SNAPSHOT_CONSENT="${SNAPSHOT_CONSENT:-none}"
SNAPSHOT_CONTAINER_DIR="/app/benchmark/privacy_testsuite/db_snapshots"

SPLITS=(
    split
    #default
    #split_3_19
    #split_10_8
    #split_nomerge_50
    #new_test
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
    docker-compose build benchmark
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

    POLICY_HOST_DIR="policies/${DIR}"
    POLICY_CONTAINER_DIR="/app/policies/${DIR}"

    if [[ ! -d "${POLICY_HOST_DIR}" ]]; then
        echo "  Split failed: ${DIR} (missing directory: ${POLICY_HOST_DIR})"
        FAILED_SPLITS+=("${DIR}")
        echo ""
        continue
    fi

    mapfile -t _mfotl_files < <(ls "${POLICY_HOST_DIR}"/*.mfotl 2>/dev/null | sort)
    if [[ ${#_mfotl_files[@]} -eq 0 ]]; then
        echo "  Split failed: ${DIR} (no .mfotl files in ${POLICY_HOST_DIR})"
        FAILED_SPLITS+=("${DIR}")
        echo ""
        continue
    fi

    STATE_LIST=""
    for mfotl_path in "${_mfotl_files[@]}"; do
        fname="$(basename "${mfotl_path}")"
        stem="${fname%.mfotl}"
        state_container_path="${SNAPSHOT_CONTAINER_DIR}/state_p${stem}_u${SNAPSHOT_USERS}_n${SNAPSHOT_TWEETS}_c${SNAPSHOT_CONSENT}.bin"
        if [[ -z "${STATE_LIST}" ]]; then
            STATE_LIST="${state_container_path}"
        else
            STATE_LIST+=",${state_container_path}"
        fi
    done

    echo "  Formula count: ${#_mfotl_files[@]}"
    echo "  Snapshot tag: u${SNAPSHOT_USERS}_n${SNAPSHOT_TWEETS}_c${SNAPSHOT_CONSENT}"

    docker-compose run --rm \
        -e PREPARE_POLICY_DIRS="${DIR}" \
        -e INSTRLIB_STATE="${STATE_LIST}" \
        benchmark \
        gdpr "${EXE}" \
        --instrlib "${INSTRLIB}" \
        --formula "${POLICY_CONTAINER_DIR}" \
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
