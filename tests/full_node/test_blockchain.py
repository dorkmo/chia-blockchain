import asyncio
import time
from typing import Any, Dict
from pathlib import Path

import pytest
from blspy import PrivateKey

from src.full_node.blockchain import Blockchain, ReceiveBlockResult
from src.full_node.store import FullNodeStore
from src.types.full_block import FullBlock
from src.types.hashable.coin import Coin
from src.types.header import Header, HeaderData
from src.types.proof_of_space import ProofOfSpace
from src.full_node.coin_store import CoinStore
from src.util.ints import uint8, uint64
from src.consensus.constants import constants as consensus_constants
from tests.block_tools import BlockTools

bt = BlockTools()
test_constants: Dict[str, Any] = consensus_constants.copy()
test_constants.update(
    {
        "DIFFICULTY_STARTING": 5,
        "DISCRIMINANT_SIZE_BITS": 16,
        "BLOCK_TIME_TARGET": 10,
        "MIN_BLOCK_TIME": 2,
        "DIFFICULTY_EPOCH": 12,  # The number of blocks per epoch
        "DIFFICULTY_DELAY": 3,  # EPOCH / WARP_FACTOR
        "MIN_ITERS_STARTING": 50 * 2,
    }
)
test_constants["GENESIS_BLOCK"] = bytes(
    bt.create_genesis_block(test_constants, bytes([0] * 32), b"0")
)


@pytest.fixture(scope="module")
def event_loop():
    loop = asyncio.get_event_loop()
    yield loop


class TestGenesisBlock:
    @pytest.mark.asyncio
    async def test_basic_blockchain(self):
        unspent_store = await CoinStore.create(Path("blockchain_test.db"))
        store = await FullNodeStore.create(Path("blockchain_test.db"))
        await store._clear_database()
        bc1 = await Blockchain.create(unspent_store, store, test_constants)
        assert len(bc1.get_current_tips()) == 1
        genesis_block = bc1.get_current_tips()[0]
        assert genesis_block.height == 0
        assert (
            bc1.get_next_difficulty(genesis_block.header_hash)
        ) == genesis_block.weight
        assert bc1.get_next_min_iters(bc1.genesis) > 0

        await unspent_store.close()
        await store.close()


class TestBlockValidation:
    @pytest.fixture(scope="module")
    async def initial_blockchain(self):
        """
        Provides a list of 10 valid blocks, as well as a blockchain with 9 blocks added to it.
        """
        blocks = bt.get_consecutive_blocks(test_constants, 10, [], 10)
        store = await FullNodeStore.create(Path("blockchain_test.db"))
        await store._clear_database()
        unspent_store = await CoinStore.create(Path("blockchain_test.db"))
        b: Blockchain = await Blockchain.create(unspent_store, store, test_constants)
        for i in range(1, 9):
            result, removed = await b.receive_block(blocks[i])
            assert result == ReceiveBlockResult.ADDED_TO_HEAD
        yield (blocks, b)

        await unspent_store.close()
        await store.close()

    @pytest.mark.asyncio
    async def test_prev_pointer(self, initial_blockchain):
        blocks, b = initial_blockchain
        block_bad = FullBlock(
            blocks[9].proof_of_space,
            blocks[9].proof_of_time,
            Header(
                HeaderData(
                    blocks[9].header.data.height,
                    bytes([1] * 32),
                    blocks[9].header.data.timestamp,
                    blocks[9].header.data.filter_hash,
                    blocks[9].header.data.proof_of_space_hash,
                    blocks[9].header.data.weight,
                    blocks[9].header.data.total_iters,
                    blocks[9].header.data.additions_root,
                    blocks[9].header.data.removals_root,
                    blocks[9].header.data.coinbase,
                    blocks[9].header.data.coinbase_signature,
                    blocks[9].header.data.fees_coin,
                    blocks[9].header.data.aggregated_signature,
                    blocks[9].header.data.cost,
                    blocks[9].header.data.extension_data,
                    blocks[9].header.data.generator_hash,
                ),
                blocks[9].header.harvester_signature,
            ),
            blocks[9].transactions_generator,
            blocks[9].transactions_filter,
        )
        result, removed = await b.receive_block(block_bad)
        assert (result) == ReceiveBlockResult.DISCONNECTED_BLOCK

    @pytest.mark.asyncio
    async def test_timestamp(self, initial_blockchain):
        blocks, b = initial_blockchain
        # Time too far in the past
        block_bad = FullBlock(
            blocks[9].proof_of_space,
            blocks[9].proof_of_time,
            Header(
                HeaderData(
                    blocks[9].header.data.height,
                    blocks[9].header.data.prev_header_hash,
                    blocks[9].header.data.timestamp - 1000,
                    blocks[9].header.data.filter_hash,
                    blocks[9].header.data.proof_of_space_hash,
                    blocks[9].header.data.weight,
                    blocks[9].header.data.total_iters,
                    blocks[9].header.data.additions_root,
                    blocks[9].header.data.removals_root,
                    blocks[9].header.data.coinbase,
                    blocks[9].header.data.coinbase_signature,
                    blocks[9].header.data.fees_coin,
                    blocks[9].header.data.aggregated_signature,
                    blocks[9].header.data.cost,
                    blocks[9].header.data.extension_data,
                    blocks[9].header.data.generator_hash,
                ),
                blocks[9].header.harvester_signature,
            ),
            blocks[9].transactions_generator,
            blocks[9].transactions_filter,
        )
        result, removed = await b.receive_block(block_bad)
        assert (result) == ReceiveBlockResult.INVALID_BLOCK

        # Time too far in the future
        block_bad = FullBlock(
            blocks[9].proof_of_space,
            blocks[9].proof_of_time,
            Header(
                HeaderData(
                    blocks[9].header.data.height,
                    blocks[9].header.data.prev_header_hash,
                    uint64(int(time.time() + 3600 * 3)),
                    blocks[9].header.data.filter_hash,
                    blocks[9].header.data.proof_of_space_hash,
                    blocks[9].header.data.weight,
                    blocks[9].header.data.total_iters,
                    blocks[9].header.data.additions_root,
                    blocks[9].header.data.removals_root,
                    blocks[9].header.data.coinbase,
                    blocks[9].header.data.coinbase_signature,
                    blocks[9].header.data.fees_coin,
                    blocks[9].header.data.aggregated_signature,
                    blocks[9].header.data.cost,
                    blocks[9].header.data.extension_data,
                    blocks[9].header.data.generator_hash,
                ),
                blocks[9].header.harvester_signature,
            ),
            blocks[9].transactions_generator,
            blocks[9].transactions_filter,
        )
        result, removed = await b.receive_block(block_bad)
        assert (result) == ReceiveBlockResult.INVALID_BLOCK

    @pytest.mark.asyncio
    async def test_generator_hash(self, initial_blockchain):
        blocks, b = initial_blockchain
        block_bad = FullBlock(
            blocks[9].proof_of_space,
            blocks[9].proof_of_time,
            Header(
                HeaderData(
                    blocks[9].header.data.height,
                    blocks[9].header.data.prev_header_hash,
                    blocks[9].header.data.timestamp,
                    blocks[9].header.data.filter_hash,
                    blocks[9].header.data.proof_of_space_hash,
                    blocks[9].header.data.weight,
                    blocks[9].header.data.total_iters,
                    blocks[9].header.data.additions_root,
                    blocks[9].header.data.removals_root,
                    blocks[9].header.data.coinbase,
                    blocks[9].header.data.coinbase_signature,
                    blocks[9].header.data.fees_coin,
                    blocks[9].header.data.aggregated_signature,
                    blocks[9].header.data.cost,
                    blocks[9].header.data.extension_data,
                    bytes([1] * 32),
                ),
                blocks[9].header.harvester_signature,
            ),
            blocks[9].transactions_generator,
            blocks[9].transactions_filter,
        )
        result, removed = await b.receive_block(block_bad)
        assert result == ReceiveBlockResult.INVALID_BLOCK

    @pytest.mark.asyncio
    async def test_harvester_signature(self, initial_blockchain):
        blocks, b = initial_blockchain
        # Time too far in the past
        block_bad = FullBlock(
            blocks[9].proof_of_space,
            blocks[9].proof_of_time,
            Header(
                blocks[9].header.data,
                PrivateKey.from_seed(b"0").sign_prepend(b"random junk"),
            ),
            blocks[9].transactions_generator,
            blocks[9].transactions_filter,
        )
        result, removed = await b.receive_block(block_bad)
        assert result == ReceiveBlockResult.INVALID_BLOCK

    @pytest.mark.asyncio
    async def test_invalid_pos(self, initial_blockchain):
        blocks, b = initial_blockchain

        bad_pos = bytearray([i for i in blocks[9].proof_of_space.proof])
        bad_pos[0] = uint8((bad_pos[0] + 1) % 256)
        # Proof of space invalid
        block_bad = FullBlock(
            ProofOfSpace(
                blocks[9].proof_of_space.challenge_hash,
                blocks[9].proof_of_space.pool_pubkey,
                blocks[9].proof_of_space.plot_pubkey,
                blocks[9].proof_of_space.size,
                bytes(bad_pos),
            ),
            blocks[9].proof_of_time,
            blocks[9].header,
            blocks[9].transactions_generator,
            blocks[9].transactions_filter,
        )
        result, removed = await b.receive_block(block_bad)
        assert result == ReceiveBlockResult.INVALID_BLOCK

    @pytest.mark.asyncio
    async def test_invalid_coinbase_height(self, initial_blockchain):
        blocks, b = initial_blockchain

        # Coinbase height invalid
        block_bad = FullBlock(
            blocks[9].proof_of_space,
            blocks[9].proof_of_time,
            Header(
                HeaderData(
                    blocks[9].header.data.height,
                    blocks[9].header.data.prev_header_hash,
                    blocks[9].header.data.timestamp,
                    blocks[9].header.data.filter_hash,
                    blocks[9].header.data.proof_of_space_hash,
                    blocks[9].header.data.weight,
                    blocks[9].header.data.total_iters,
                    blocks[9].header.data.additions_root,
                    blocks[9].header.data.removals_root,
                    Coin(
                        blocks[9].header.data.coinbase.parent_coin_info,
                        blocks[9].header.data.coinbase.puzzle_hash,
                        uint64(9999999999),
                    ),
                    blocks[9].header.data.coinbase_signature,
                    blocks[9].header.data.fees_coin,
                    blocks[9].header.data.aggregated_signature,
                    blocks[9].header.data.cost,
                    blocks[9].header.data.extension_data,
                    blocks[9].header.data.generator_hash,
                ),
                blocks[9].header.harvester_signature,
            ),
            blocks[9].transactions_generator,
            blocks[9].transactions_filter,
        )
        result, removed = await b.receive_block(block_bad)
        assert result == ReceiveBlockResult.INVALID_BLOCK

    @pytest.mark.asyncio
    async def test_difficulty_change(self):
        num_blocks = 30
        # Make it 5x faster than target time
        blocks = bt.get_consecutive_blocks(test_constants, num_blocks, [], 2)

        unspent_store = await CoinStore.create(Path("blockchain_test.db"))
        store = await FullNodeStore.create(Path("blockchain_test.db"))
        await store._clear_database()
        b: Blockchain = await Blockchain.create(unspent_store, store, test_constants)
        for i in range(1, num_blocks):
            result, removed = await b.receive_block(blocks[i])
            assert result == ReceiveBlockResult.ADDED_TO_HEAD

        diff_25 = b.get_next_difficulty(blocks[24].header_hash)
        diff_26 = b.get_next_difficulty(blocks[25].header_hash)
        diff_27 = b.get_next_difficulty(blocks[26].header_hash)

        assert diff_26 == diff_25
        assert diff_27 > diff_26
        assert (diff_27 / diff_26) <= test_constants["DIFFICULTY_FACTOR"]

        assert (b.get_next_min_iters(blocks[1])) == test_constants["MIN_ITERS_STARTING"]
        assert (b.get_next_min_iters(blocks[24])) == (b.get_next_min_iters(blocks[23]))
        assert (b.get_next_min_iters(blocks[25])) == (b.get_next_min_iters(blocks[24]))
        assert (b.get_next_min_iters(blocks[26])) > (b.get_next_min_iters(blocks[25]))
        assert (b.get_next_min_iters(blocks[27])) == (b.get_next_min_iters(blocks[26]))

        await unspent_store.close()
        await store.close()


class TestReorgs:
    @pytest.mark.asyncio
    async def test_basic_reorg(self):
        blocks = bt.get_consecutive_blocks(test_constants, 100, [], 9)
        unspent_store = await CoinStore.create(Path("blockchain_test.db"))
        store = await FullNodeStore.create(Path("blockchain_test.db"))
        await store._clear_database()
        b: Blockchain = await Blockchain.create(unspent_store, store, test_constants)

        for i in range(1, len(blocks)):
            await b.receive_block(blocks[i])
        assert b.get_current_tips()[0].height == 100

        blocks_reorg_chain = bt.get_consecutive_blocks(
            test_constants, 30, blocks[:90], 9, b"2"
        )
        for i in range(1, len(blocks_reorg_chain)):
            reorg_block = blocks_reorg_chain[i]
            result, removed = await b.receive_block(reorg_block)
            if reorg_block.height < 90:
                assert result == ReceiveBlockResult.ALREADY_HAVE_BLOCK
            elif reorg_block.height < 99:
                assert result == ReceiveBlockResult.ADDED_AS_ORPHAN
            elif reorg_block.height >= 100:
                assert result == ReceiveBlockResult.ADDED_TO_HEAD
        assert b.get_current_tips()[0].height == 119

        await unspent_store.close()
        await store.close()

    @pytest.mark.asyncio
    async def test_reorg_from_genesis(self):
        blocks = bt.get_consecutive_blocks(test_constants, 20, [], 9, b"0")
        unspent_store = await CoinStore.create(Path("blockchain_test.db"))
        store = await FullNodeStore.create(Path("blockchain_test.db"))
        await store._clear_database()
        b: Blockchain = await Blockchain.create(unspent_store, store, test_constants)
        for i in range(1, len(blocks)):
            await b.receive_block(blocks[i])
        assert b.get_current_tips()[0].height == 20

        # Reorg from genesis
        blocks_reorg_chain = bt.get_consecutive_blocks(
            test_constants, 21, [blocks[0]], 9, b"3"
        )
        for i in range(1, len(blocks_reorg_chain)):
            reorg_block = blocks_reorg_chain[i]
            result, removed = await b.receive_block(reorg_block)
            if reorg_block.height == 0:
                assert result == ReceiveBlockResult.ALREADY_HAVE_BLOCK
            elif reorg_block.height < 19:
                assert result == ReceiveBlockResult.ADDED_AS_ORPHAN
            else:
                assert result == ReceiveBlockResult.ADDED_TO_HEAD
        assert b.get_current_tips()[0].height == 21

        # Reorg back to original branch
        blocks_reorg_chain_2 = bt.get_consecutive_blocks(
            test_constants, 3, blocks[:-1], 9, b"4"
        )
        result, _ = await b.receive_block(blocks_reorg_chain_2[20])
        assert result == ReceiveBlockResult.ADDED_AS_ORPHAN

        result, _ = await b.receive_block(blocks_reorg_chain_2[21])
        assert result == ReceiveBlockResult.ADDED_TO_HEAD

        result, _ = await b.receive_block(blocks_reorg_chain_2[22])
        assert result == ReceiveBlockResult.ADDED_TO_HEAD

        await unspent_store.close()
        await store.close()

    @pytest.mark.asyncio
    async def test_lca(self):
        blocks = bt.get_consecutive_blocks(test_constants, 5, [], 9, b"0")
        unspent_store = await CoinStore.create(Path("blockchain_test.db"))
        store = await FullNodeStore.create(Path("blockchain_test.db"))
        await store._clear_database()
        b: Blockchain = await Blockchain.create(unspent_store, store, test_constants)
        for i in range(1, len(blocks)):
            await b.receive_block(blocks[i])

        assert b.lca_block.header_hash == blocks[3].header_hash
        block_5_2 = bt.get_consecutive_blocks(test_constants, 1, blocks[:5], 9, b"1")
        block_5_3 = bt.get_consecutive_blocks(test_constants, 1, blocks[:5], 9, b"2")

        await b.receive_block(block_5_2[5])
        assert b.lca_block.header_hash == blocks[4].header_hash
        await b.receive_block(block_5_3[5])
        assert b.lca_block.header_hash == blocks[4].header_hash

        reorg = bt.get_consecutive_blocks(test_constants, 6, [], 9, b"3")
        for i in range(1, len(reorg)):
            await b.receive_block(reorg[i])
        assert b.lca_block.header_hash == blocks[0].header_hash

        await unspent_store.close()
        await store.close()

    @pytest.mark.asyncio
    async def test_get_header_hashes(self):
        blocks = bt.get_consecutive_blocks(test_constants, 5, [], 9, b"0")
        unspent_store = await CoinStore.create(Path("blockchain_test.db"))
        store = await FullNodeStore.create(Path("blockchain_test.db"))
        await store._clear_database()
        b: Blockchain = await Blockchain.create(unspent_store, store, test_constants)

        for i in range(1, len(blocks)):
            await b.receive_block(blocks[i])
        header_hashes = b.get_header_hashes(blocks[-1].header_hash)
        assert len(header_hashes) == 6
        assert header_hashes == [block.header_hash for block in blocks]

        await unspent_store.close()
        await store.close()
