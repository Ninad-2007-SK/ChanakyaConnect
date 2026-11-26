# ChanakyaConnect
Python DSA student networking project. No third-party Python packages required.

## Render deployment
Create a free Python Web Service from this repository. Build command: `python -m py_compile chanakya_connect.py`. Start command: `python chanakya_connect.py`. Set `SUPABASE_URL` and `SUPABASE_SERVICE_KEY` as secret environment variables. Health check: `/health`. Use one server instance only. Never commit keys. The Supabase network_state table must already exist with service_role access and RLS enabled.

## Limitations
Educational demo only; use fictional accounts and unique test passwords. Cloud images limited to 256 KB and stored in the JSON row. Sessions reset on restart; users can log in again. The single-row snapshot architecture is not intended for large-scale or multi-instance deployment. If storage fails, restart the service after resolving the problem. Existing local accounts are not migrated. Local execution without cloud variables uses local JSON.
