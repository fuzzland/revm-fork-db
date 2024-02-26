use crate::utils;
use alloy_rpc_types::Block;
use anyhow::{anyhow, Context};
use revm::{
    db::{CacheDB, DatabaseRef},
    interpreter,
    precompile::Bytes,
    primitives::{alloy_primitives::U64, keccak256, AccountInfo, Address, Bytecode, B256, U256},
    Database,
};
use serde::de::DeserializeOwned;
use serde_json::{json, Value};
use std::time::Duration;
use std::{
    sync::atomic::{AtomicU64, Ordering},
    time,
};

pub struct ForkDB {
    rpc_client: MiniRpcClient,
    block_number: u64,
    measure_rpc_time: bool,
    cumulative_rpc_time: AtomicU64,
}

impl ForkDB {
    pub fn new<T: Into<String>, B: Into<u64>>(rpc_url: T, block_number: B) -> Self {
        ForkDB {
            rpc_client: MiniRpcClient::new(rpc_url),
            block_number: block_number.into(),
            measure_rpc_time: false,
            cumulative_rpc_time: AtomicU64::new(0),
        }
    }

    pub fn new_as_cache_db<T: Into<String>, B: Into<u64>>(
        rpc_url: T,
        block_number: B,
    ) -> CacheDB<Self> {
        CacheDB::new(ForkDB::new(rpc_url, block_number))
    }

    pub fn with_measure_rpc_time<T: Into<String>, B: Into<u64>>(mut self, enable: bool) -> Self {
        self.measure_rpc_time = enable;
        self
    }

    pub fn get_rpc_time(&self) -> Duration {
        Duration::from_millis(self.cumulative_rpc_time.load(Ordering::Relaxed))
    }

    pub fn reset_rpc_time(&mut self) {
        self.cumulative_rpc_time.store(0, Ordering::Relaxed);
    }

    pub fn make_request<F, R>(&self, f: F) -> anyhow::Result<R>
    where
        F: FnOnce(&MiniRpcClient) -> anyhow::Result<R>,
    {
        if self.measure_rpc_time {
            let start = time::Instant::now();
            let result = f(&self.rpc_client)?;
            let elapsed = start.elapsed().as_millis() as u64;
            self.cumulative_rpc_time
                .fetch_add(elapsed, Ordering::Relaxed);
            Ok(result)
        } else {
            f(&self.rpc_client)
        }
    }
}

impl Database for ForkDB {
    type Error = anyhow::Error;

    fn basic(&mut self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        DatabaseRef::basic_ref(self, address)
    }

    fn code_by_hash(&mut self, code_hash: B256) -> Result<Bytecode, Self::Error> {
        DatabaseRef::code_by_hash_ref(self, code_hash)
    }

    fn storage(&mut self, address: Address, index: U256) -> Result<U256, Self::Error> {
        DatabaseRef::storage_ref(self, address, index)
    }

    fn block_hash(&mut self, number: U256) -> Result<B256, Self::Error> {
        DatabaseRef::block_hash_ref(self, number)
    }
}

impl DatabaseRef for ForkDB {
    type Error = anyhow::Error;

    fn basic_ref(&self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        let (balance, nonce, code) = self
            .make_request(|rpc_client| rpc_client.get_account_basic(&address, self.block_number))?;

        let code_hash = keccak256(&code);
        let bytecode = interpreter::analysis::to_analysed(Bytecode::new_raw(code));

        Ok(Some(AccountInfo::new(balance, nonce, code_hash, bytecode)))
    }

    fn code_by_hash_ref(&self, _code_hash: B256) -> Result<Bytecode, Self::Error> {
        unreachable!("code_by_hash should not be called")
    }

    fn storage_ref(&self, address: Address, index: U256) -> Result<U256, Self::Error> {
        let result = self.make_request(|rpc_client| {
            rpc_client.get_storage_at(&address, &index.into(), self.block_number)
        })?;

        Ok(result.into())
    }

    fn block_hash_ref(&self, number: U256) -> Result<B256, Self::Error> {
        let number = match utils::u256_to_u64(&number) {
            Some(number) => number,
            None => anyhow::bail!("block number too large"),
        };

        let block = self
            .make_request(|rpc_client| rpc_client.get_block(number))?
            .context("block not found")?;

        block.header.hash.context("block not finalized")
    }
}

pub struct MiniRpcClient {
    client: ureq::Agent,
    rpc_url: String,
}

impl MiniRpcClient {
    pub fn new<T: Into<String>>(rpc_url: T) -> Self {
        MiniRpcClient {
            rpc_url: rpc_url.into(),
            client: ureq::Agent::new(),
        }
    }

    fn format_block_tag(block_number: u64) -> Value {
        json!(format!("0x{:x}", block_number))
    }

    fn make_request(id: u64, method: &str, params: &Value) -> Value {
        json!({
            "id": id,
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
        })
    }

    fn handle_response<T: DeserializeOwned>(mut response: Value) -> anyhow::Result<T> {
        if let Some(error) = response.get("error") {
            anyhow::bail!("rpc error: {error}");
        } else if response.get("result").is_some() {
            let value = response["result"].take();
            return serde_json::from_value(value).context("fail to deserialize result");
        } else {
            anyhow::bail!("rpc response missing result")
        }
    }

    fn do_request<T: DeserializeOwned>(&self, method: &str, params: Value) -> anyhow::Result<T> {
        let request = Self::make_request(1, method, &params);

        let response = self
            .client
            .post(&self.rpc_url)
            .send_json(request)
            .context("fail to send request")?
            .into_json::<Value>()
            .context("fail to read response")?;

        tracing::trace!(
            method,
            params = format_args!("{}", params),
            "response: {response}",
        );

        Self::handle_response(response)
    }

    fn get_storage_at(
        &self,
        address: &Address,
        index: &B256,
        block_number: u64,
    ) -> anyhow::Result<B256> {
        let response = self.do_request::<B256>(
            "eth_getStorageAt",
            json!([
                address.to_string(),
                index.to_string(),
                Self::format_block_tag(block_number),
            ]),
        )?;

        Ok(response)
    }

    fn get_block(&self, block_number: u64) -> anyhow::Result<Option<Block>> {
        let response = self.do_request::<Option<Block>>(
            "eth_getBlockByNumber",
            json!([Self::format_block_tag(block_number), false]),
        )?;

        Ok(response)
    }

    fn get_account_basic(
        &self,
        address: &Address,
        block_number: u64,
    ) -> anyhow::Result<(U256, u64, Bytes)> {
        let requests = json!([
            Self::make_request(
                1,
                "eth_getBalance",
                &json!([address.to_string(), Self::format_block_tag(block_number)]),
            ),
            Self::make_request(
                2,
                "eth_getTransactionCount",
                &json!([address.to_string(), Self::format_block_tag(block_number)]),
            ),
            Self::make_request(
                3,
                "eth_getCode",
                &json!([address.to_string(), Self::format_block_tag(block_number)]),
            ),
        ]);

        let mut response = self
            .client
            .post(&self.rpc_url)
            .send_json(requests)
            .context("fail to send request")?
            .into_json::<Value>()?;

        tracing::trace!(
            account = address.to_string(),
            "get account basic info. response: {response}"
        );

        let results = response
            .as_array_mut()
            .ok_or(anyhow!("expect array response"))?;

        if results.len() != 3 {
            anyhow::bail!("expect 3 responses, got {}", results.len());
        }

        let balance =
            Self::handle_response::<U256>(results[0].take()).context("fail to parse balance")?;
        let nonce =
            Self::handle_response::<U64>(results[1].take()).context("fail to parse nonce")?;
        let code =
            Self::handle_response::<Bytes>(results[2].take()).context("fail to parse code")?;

        Ok((balance, nonce.as_limbs()[0], code))
    }
}