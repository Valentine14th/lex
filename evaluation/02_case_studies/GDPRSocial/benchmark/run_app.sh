#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "${SCRIPT_DIR}/.."   # -> GDPRSocial/

# Ignore any caller-provided compose file override; always use repo-local compose.
unset COMPOSE_FILE

# Usage:
#   ./benchmark/run_app_split.sh [split-name]
#
# Example:
#   ./benchmark/run_app_split.sh default
#   ./benchmark/run_app_split.sh split
DIR="${1:-default}"

EXE="${EXE:-/opt/whyenf/enfguard}"
SNAPSHOT_USERS="${SNAPSHOT_USERS:-1}"
SNAPSHOT_TWEETS="${SNAPSHOT_TWEETS:-100}"
SNAPSHOT_CONSENT="${SNAPSHOT_CONSENT:-none}"
SNAPSHOT_CONTAINER_DIR="${SNAPSHOT_CONTAINER_DIR:-/app/benchmark/privacy_testsuite/db_snapshots}"
HOST_LOG_DIR="${HOST_LOG_DIR:-output/app_runs}"

POLICY_HOST_DIR="policies/${DIR}"
POLICY_CONTAINER_DIR="/app/policies/${DIR}"

if [[ ! -d "${POLICY_HOST_DIR}" ]]; then
    echo "Missing directory: ${POLICY_HOST_DIR}" >&2
    exit 1
fi

mapfile -t _mfotl_files < <(ls "${POLICY_HOST_DIR}"/*.mfotl 2>/dev/null | sort)
if [[ ${#_mfotl_files[@]} -eq 0 ]]; then
    echo "No .mfotl files in ${POLICY_HOST_DIR}" >&2
    exit 1
fi

mapfile -t _sig_files < <(ls "${POLICY_HOST_DIR}"/*.sig 2>/dev/null | sort)
if [[ ${#_sig_files[@]} -eq 0 ]]; then
    echo "No .sig files in ${POLICY_HOST_DIR}" >&2
    exit 1
fi

STATE_LIST=""
FORMULA_LIST=""
SIG_LIST=""

for mfotl_path in "${_mfotl_files[@]}"; do
    fname="$(basename "${mfotl_path}")"
    stem="${fname%.mfotl}"

    state_container_path="${SNAPSHOT_CONTAINER_DIR}/state_p${stem}_u${SNAPSHOT_USERS}_n${SNAPSHOT_TWEETS}_c${SNAPSHOT_CONSENT}.bin"
    formula_container_path="${POLICY_CONTAINER_DIR}/${fname}"

    if [[ -z "${STATE_LIST}" ]]; then
        STATE_LIST="${state_container_path}"
        FORMULA_LIST="${formula_container_path}"
    else
        STATE_LIST+=",${state_container_path}"
        FORMULA_LIST+=",${formula_container_path}"
    fi
done

for sig_path in "${_sig_files[@]}"; do
    sig_name="$(basename "${sig_path}")"
    sig_container_path="${POLICY_CONTAINER_DIR}/${sig_name}"
    if [[ -z "${SIG_LIST}" ]]; then
        SIG_LIST="${sig_container_path}"
    else
        SIG_LIST+=",${sig_container_path}"
    fi
done

RUN_TS="$(date +%Y%m%d_%H%M%S)"
mkdir -p "${HOST_LOG_DIR}"
HOST_LOG_PATH="${HOST_LOG_DIR}/app_${DIR}_${RUN_TS}.log"

echo "══════════════════════════════════════════════════════════"
echo "  App run: policies/${DIR}"
echo "══════════════════════════════════════════════════════════"
echo "  Formula count: ${#_mfotl_files[@]}"
echo "  Snapshot tag: u${SNAPSHOT_USERS}_n${SNAPSHOT_TWEETS}_c${SNAPSHOT_CONSENT}"
echo "  Host log: ${HOST_LOG_PATH}"
echo ""
echo "  URL: http://127.0.0.1:8000/"
echo "  Login: http://127.0.0.1:8000/accounts/login/"
echo ""

docker-compose run --rm --service-ports \
    -e INSTRLIB_EXE="${EXE}" \
    -e INSTRLIB_FORMULA="${FORMULA_LIST}" \
    -e INSTRLIB_SIG="${SIG_LIST}" \
    -e INSTRLIB_STATE="${STATE_LIST}" \
    --entrypoint python3 \
    benchmark \
    manage.py runserver 0.0.0.0:8000 \
    > >(tee "${HOST_LOG_PATH}") 2>&1
