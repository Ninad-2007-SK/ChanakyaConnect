import base64
import hashlib
import hmac
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import mimetypes
import os
import re
import socket
import sys
import threading
import time
import urllib.parse
import urllib.request
import urllib.error
import uuid
import webbrowser


# ==============================================================================
# 1. DYNAMIC ARRAY
# ==============================================================================
class DynamicArray:
    """Resizable contiguous array with O(1) indexed access and amortized O(1) append."""

    def __init__(self, initial_capacity=8):
        self._capacity = max(4, initial_capacity)
        self._size = 0
        self._data = [None] * self._capacity

    def _resize(self, new_capacity):
        new_data = [None] * new_capacity
        for i in range(self._size):
            new_data[i] = self._data[i]
        self._data = new_data
        self._capacity = new_capacity

    def append(self, item):
        if self._size == self._capacity:
            self._resize(self._capacity * 2)
        self._data[self._size] = item
        self._size += 1

    def pop(self, index=-1):
        if self._size == 0:
            raise IndexError("Pop from empty DynamicArray")
        if index < 0:
            index += self._size
        if index < 0 or index >= self._size:
            raise IndexError("Index out of range")
        item = self._data[index]
        for i in range(index, self._size - 1):
            self._data[i] = self._data[i + 1]
        self._data[self._size - 1] = None
        self._size -= 1
        return item

    def get(self, index):
        if index < 0:
            index += self._size
        if index < 0 or index >= self._size:
            raise IndexError("Index out of range")
        return self._data[index]

    def set(self, index, value):
        if index < 0:
            index += self._size
        if index < 0 or index >= self._size:
            raise IndexError("Index out of range")
        self._data[index] = value

    def clear(self):
        self._capacity = 8
        self._size = 0
        self._data = [None] * self._capacity

    def to_list(self):
        return [self._data[i] for i in range(self._size)]

    def __len__(self):
        return self._size

    def __getitem__(self, index):
        return self.get(index)

    def __setitem__(self, index, value):
        self.set(index, value)

    def __iter__(self):
        for i in range(self._size):
            yield self._data[i]


# ==============================================================================
# 2. HASH TABLE & HASH SET
# ==============================================================================
class _HashNode:
    def __init__(self, key, value):
        self.key = key
        self.value = value
        self.next = None


class HashTable:
    """Separate-chaining hash map with polynomial rolling hash. Average O(1) ops."""

    def __init__(self, initial_buckets=16):
        self._num_buckets = max(8, initial_buckets)
        self._buckets = [None] * self._num_buckets
        self._size = 0

    def _hash(self, key):
        h = 0
        for ch in str(key):
            h = (h * 31 + ord(ch)) & 0x7FFFFFFF
        return h % self._num_buckets

    def _rehash(self):
        old_buckets = self._buckets
        self._num_buckets *= 2
        self._buckets = [None] * self._num_buckets
        self._size = 0
        for head in old_buckets:
            curr = head
            while curr is not None:
                self.put(curr.key, curr.value)
                curr = curr.next

    def put(self, key, value):
        if (self._size + 1) / self._num_buckets > 0.75:
            self._rehash()
        idx = self._hash(key)
        curr = self._buckets[idx]
        while curr is not None:
            if curr.key == key:
                curr.value = value
                return
            curr = curr.next
        node = _HashNode(key, value)
        node.next = self._buckets[idx]
        self._buckets[idx] = node
        self._size += 1

    def get(self, key, default=None):
        idx = self._hash(key)
        curr = self._buckets[idx]
        while curr is not None:
            if curr.key == key:
                return curr.value
            curr = curr.next
        return default

    def contains(self, key):
        idx = self._hash(key)
        curr = self._buckets[idx]
        while curr is not None:
            if curr.key == key:
                return True
            curr = curr.next
        return False

    def remove(self, key):
        idx = self._hash(key)
        curr = self._buckets[idx]
        prev = None
        while curr is not None:
            if curr.key == key:
                if prev is None:
                    self._buckets[idx] = curr.next
                else:
                    prev.next = curr.next
                self._size -= 1
                return True
            prev = curr
            curr = curr.next
        return False

    def keys(self):
        res = DynamicArray()
        for head in self._buckets:
            curr = head
            while curr is not None:
                res.append(curr.key)
                curr = curr.next
        return res

    def values(self):
        res = DynamicArray()
        for head in self._buckets:
            curr = head
            while curr is not None:
                res.append(curr.value)
                curr = curr.next
        return res

    def items(self):
        res = DynamicArray()
        for head in self._buckets:
            curr = head
            while curr is not None:
                res.append((curr.key, curr.value))
                curr = curr.next
        return res

    def __len__(self):
        return self._size

    def __contains__(self, key):
        return self.contains(key)

    def __iter__(self):
        for head in self._buckets:
            curr = head
            while curr is not None:
                yield curr.key
                curr = curr.next


class HashSet:
    """Unique element set backed by HashTable with O(min(|A|, |B|)) intersection."""

    def __init__(self, iterable=None):
        self._table = HashTable()
        if iterable is not None:
            for item in iterable:
                self.add(item)

    def add(self, item):
        self._table.put(item, True)

    def remove(self, item):
        return self._table.remove(item)

    def contains(self, item):
        return self._table.contains(item)

    def intersection(self, other):
        res = HashSet()
        smaller, larger = (self, other) if len(self) <= len(other) else (other, self)
        for item in smaller:
            if larger.contains(item):
                res.add(item)
        return res

    def to_list(self):
        return self._table.keys().to_list()

    def __len__(self):
        return len(self._table)

    def __contains__(self, item):
        return self.contains(item)

    def __iter__(self):
        return iter(self._table)


# ==============================================================================
# 3. STACK (LIFO) & QUEUE (FIFO)
# ==============================================================================
class Stack:
    """LIFO Stack for Undo history, Back navigation, and iterative DFS."""

    def __init__(self, max_size=100):
        self._items = DynamicArray()
        self._max_size = max_size

    def push(self, item):
        if len(self._items) >= self._max_size:
            self._items.pop(0)
        self._items.append(item)

    def pop(self):
        if self.is_empty():
            raise IndexError("Pop from empty Stack")
        return self._items.pop()

    def peek(self):
        return None if self.is_empty() else self._items.get(len(self._items) - 1)

    def is_empty(self):
        return len(self._items) == 0

    def to_list(self):
        return self._items.to_list()

    def __len__(self):
        return len(self._items)


class _QueueNode:
    def __init__(self, value):
        self.value = value
        self.next = None


class Queue:
    """Linked-list FIFO Queue with O(1) enqueue/dequeue for BFS, requests & notifications."""

    def __init__(self):
        self._head = None
        self._tail = None
        self._size = 0

    def enqueue(self, item):
        node = _QueueNode(item)
        if self._tail is None:
            self._head = node
            self._tail = node
        else:
            self._tail.next = node
            self._tail = node
        self._size += 1

    def dequeue(self):
        if self._head is None:
            raise IndexError("Dequeue from empty Queue")
        val = self._head.value
        self._head = self._head.next
        if self._head is None:
            self._tail = None
        self._size -= 1
        return val

    def remove_matching(self, predicate):
        curr = self._head
        prev = None
        removed = False
        while curr is not None:
            if predicate(curr.value):
                removed = True
                self._size -= 1
                if prev is None:
                    self._head = curr.next
                    if self._head is None:
                        self._tail = None
                    curr = self._head
                else:
                    prev.next = curr.next
                    if curr.next is None:
                        self._tail = prev
                    curr = curr.next
            else:
                prev = curr
                curr = curr.next
        return removed

    def is_empty(self):
        return self._size == 0

    def clear(self):
        self._head = None
        self._tail = None
        self._size = 0

    def to_list(self):
        res = []
        curr = self._head
        while curr is not None:
            res.append(curr.value)
            curr = curr.next
        return res

    def __len__(self):
        return self._size

    def __iter__(self):
        curr = self._head
        while curr is not None:
            yield curr.value
            curr = curr.next


# ==============================================================================
# 4. MAX-HEAP, TRIE, COMMENT TREE, DISJOINT SET UNION
# ==============================================================================
class MaxHeap:
    """Binary Max-Heap over DynamicArray. Push & pop_max run in O(log n)."""

    def __init__(self):
        self._heap = DynamicArray()

    def _sift_up(self, idx):
        while idx > 0:
            parent = (idx - 1) // 2
            if self._heap[idx][0] > self._heap[parent][0]:
                self._heap[idx], self._heap[parent] = self._heap[parent], self._heap[idx]
                idx = parent
            else:
                break

    def _sift_down(self, idx):
        n = len(self._heap)
        while True:
            largest = idx
            left, right = 2 * idx + 1, 2 * idx + 2
            if left < n and self._heap[left][0] > self._heap[largest][0]:
                largest = left
            if right < n and self._heap[right][0] > self._heap[largest][0]:
                largest = right
            if largest != idx:
                self._heap[idx], self._heap[largest] = self._heap[largest], self._heap[idx]
                idx = largest
            else:
                break

    def push(self, priority, item):
        self._heap.append((priority, item))
        self._sift_up(len(self._heap) - 1)

    def pop_max(self):
        if len(self._heap) == 0:
            raise IndexError("Pop from empty MaxHeap")
        top = self._heap[0]
        last = self._heap.pop()
        if len(self._heap) > 0:
            self._heap[0] = last
            self._sift_down(0)
        return top

    def is_empty(self):
        return len(self._heap) == 0


class _TrieNode:
    def __init__(self):
        self.children = HashTable(initial_buckets=8)
        self.usernames = HashSet()


class Trie:
    """Prefix Tree for live as-you-type autocomplete search by name or username."""

    def __init__(self):
        self.root = _TrieNode()

    def insert(self, key_text, username):
        text = key_text.strip().lower()
        if not text:
            return
        node = self.root
        for ch in text:
            child = node.children.get(ch)
            if child is None:
                child = _TrieNode()
                node.children.put(ch, child)
            node = child
        node.usernames.add(username)

    def remove(self, key_text, username):
        text = key_text.strip().lower()
        node = self.root
        for ch in text:
            child = node.children.get(ch)
            if child is None:
                return
            node = child
        node.usernames.remove(username)

    def search_prefix(self, prefix, limit=10):
        results = DynamicArray()
        seen = HashSet()
        clean = prefix.strip().lower()
        if not clean:
            return results

        node = self.root
        for ch in clean:
            child = node.children.get(ch)
            if child is None:
                return results
            node = child

        dfs_stack = Stack(max_size=10000)
        dfs_stack.push(node)
        while not dfs_stack.is_empty() and len(results) < limit:
            curr = dfs_stack.pop()
            for uname in curr.usernames:
                if not seen.contains(uname):
                    seen.add(uname)
                    results.append(uname)
                    if len(results) >= limit:
                        break
            if len(results) >= limit:
                break
            child_keys = curr.children.keys().to_list()
            child_keys.sort(reverse=True)
            for ch in child_keys:
                dfs_stack.push(curr.children.get(ch))
        return results


class CommentTreeNode:
    """Node in an N-ary Comment Tree supporting nested replies."""

    def __init__(self, comment_id, author, text, timestamp):
        self.comment_id = comment_id
        self.author = author
        self.text = text
        self.timestamp = timestamp
        self.replies = DynamicArray()

    def to_dict(self):
        return {
            "comment_id": self.comment_id,
            "author": self.author,
            "text": self.text,
            "timestamp": self.timestamp,
            "replies": [r.to_dict() for r in self.replies],
        }

    @classmethod
    def from_dict(cls, data):
        node = cls(data["comment_id"], data["author"], data["text"], data["timestamp"])
        for r in data.get("replies", []):
            node.replies.append(cls.from_dict(r))
        return node


class CommentTree:
    """N-ary tree for comments and nested replies, searched via DFS Stack."""

    def __init__(self):
        self.top_level = DynamicArray()

    def add_comment(self, comment_id, author, text, timestamp, parent_comment_id=None):
        node = CommentTreeNode(comment_id, author, text, timestamp)
        if not parent_comment_id:
            self.top_level.append(node)
            return node
        parent = self.find_comment(parent_comment_id)
        if parent is None:
            return None
        parent.replies.append(node)
        return node

    def find_comment(self, target_id):
        stack = Stack(max_size=5000)
        for c in self.top_level:
            stack.push(c)
        while not stack.is_empty():
            node = stack.pop()
            if node.comment_id == target_id:
                return node
            for r in node.replies:
                stack.push(r)
        return None

    def count_all(self):
        total = 0
        stack = Stack(max_size=5000)
        for c in self.top_level:
            stack.push(c)
        while not stack.is_empty():
            node = stack.pop()
            total += 1
            for r in node.replies:
                stack.push(r)
        return total

    def to_list(self):
        return [c.to_dict() for c in self.top_level]

    @classmethod
    def from_list(cls, items):
        tree = cls()
        for item in items:
            tree.top_level.append(CommentTreeNode.from_dict(item))
        return tree


class DisjointSetUnion:
    """Union-Find with path halving & union by rank for campus community detection."""

    def __init__(self):
        self.parent = HashTable()
        self.rank = HashTable()

    def make_set(self, x):
        if not self.parent.contains(x):
            self.parent.put(x, x)
            self.rank.put(x, 0)

    def find(self, x):
        self.make_set(x)
        curr = x
        while self.parent.get(curr) != curr:
            p = self.parent.get(curr)
            self.parent.put(curr, self.parent.get(p))
            curr = p
        return curr

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        rank_a, rank_b = self.rank.get(ra), self.rank.get(rb)
        if rank_a < rank_b:
            self.parent.put(ra, rb)
        elif rank_a > rank_b:
            self.parent.put(rb, ra)
        else:
            self.parent.put(rb, ra)
            self.rank.put(ra, rank_a + 1)
        return True


# ==============================================================================
# 5. SOCIAL GRAPH G(V, E) WITH ADJACENCY LISTS
# ==============================================================================
class SocialGraph:
    """
    Graph G(V, E) stored via Adjacency Lists (HashTable -> HashSet).
    - Undirected edges for accepted connections (no self-edges, no duplicate edges).
    - Directed pending edges stored in outgoing HashSet & incoming FIFO Queue.
    """

    def __init__(self):
        self.adj_list = HashTable()
        self.incoming_requests = HashTable()
        self.outgoing_requests = HashTable()

    def add_vertex(self, username):
        if not self.adj_list.contains(username):
            self.adj_list.put(username, HashSet())
            self.incoming_requests.put(username, Queue())
            self.outgoing_requests.put(username, HashSet())

    def has_vertex(self, username):
        return self.adj_list.contains(username)

    def are_connected(self, u, v):
        neighbors = self.adj_list.get(u)
        return neighbors is not None and neighbors.contains(v)

    def has_pending_request(self, sender, receiver):
        out_set = self.outgoing_requests.get(sender)
        return out_set is not None and out_set.contains(receiver)

    def send_request(self, sender, receiver, timestamp):
        if sender == receiver:
            return False, "Cannot connect with yourself."
        if not self.has_vertex(sender) or not self.has_vertex(receiver):
            return False, "User does not exist."
        if self.are_connected(sender, receiver):
            return False, "You are already connected."
        if self.has_pending_request(sender, receiver):
            return False, "Connection request already sent."
        if self.has_pending_request(receiver, sender):
            return self.accept_request(receiver, sender)

        self.outgoing_requests.get(sender).add(receiver)
        self.incoming_requests.get(receiver).enqueue({"from": sender, "timestamp": timestamp})
        return True, "Connection request sent."

    def accept_request(self, sender, receiver):
        if not self.has_pending_request(sender, receiver):
            return False, "No pending request from this user."
        self.outgoing_requests.get(sender).remove(receiver)
        self.incoming_requests.get(receiver).remove_matching(lambda r: r["from"] == sender)
        self.add_undirected_edge(sender, receiver)
        return True, f"Connected with {sender}."

    def reject_request(self, sender, receiver):
        if not self.has_pending_request(sender, receiver):
            return False, "No pending request from this user."
        self.outgoing_requests.get(sender).remove(receiver)
        self.incoming_requests.get(receiver).remove_matching(lambda r: r["from"] == sender)
        return True, f"Rejected request from {sender}."

    def cancel_request(self, sender, receiver):
        if not self.has_pending_request(sender, receiver):
            return False, "No outgoing request to this user."
        self.outgoing_requests.get(sender).remove(receiver)
        self.incoming_requests.get(receiver).remove_matching(lambda r: r["from"] == sender)
        return True, f"Cancelled request to {receiver}."

    def add_undirected_edge(self, u, v):
        if u == v:
            return False
        self.add_vertex(u)
        self.add_vertex(v)
        self.adj_list.get(u).add(v)
        self.adj_list.get(v).add(u)
        return True

    def remove_connection(self, u, v):
        if not self.are_connected(u, v):
            return False, "Users are not connected."
        self.adj_list.get(u).remove(v)
        self.adj_list.get(v).remove(u)
        return True, f"Removed connection with {v}."

    def get_connections(self, username):
        neighbors = self.adj_list.get(username)
        return [] if neighbors is None else neighbors.to_list()

    def get_mutual_connections(self, u, v):
        nu, nv = self.adj_list.get(u), self.adj_list.get(v)
        if nu is None or nv is None:
            return []
        return nu.intersection(nv).to_list()

    def bfs_shortest_path(self, start, target):
        """BFS using Queue to compute degree of connection and one shortest chain."""
        if not self.has_vertex(start) or not self.has_vertex(target):
            return None, []
        if start == target:
            return 0, [start]

        visited = HashSet()
        parent = HashTable()
        q = Queue()
        visited.add(start)
        q.enqueue(start)

        found = False
        while not q.is_empty():
            curr = q.dequeue()
            if curr == target:
                found = True
                break
            neighbors = self.adj_list.get(curr)
            if neighbors is None:
                continue
            for nxt in sorted(neighbors.to_list()):
                if not visited.contains(nxt):
                    visited.add(nxt)
                    parent.put(nxt, curr)
                    q.enqueue(nxt)

        if not found:
            return None, []

        rev_stack = Stack(max_size=len(self.adj_list) + 5)
        node = target
        while node is not None:
            rev_stack.push(node)
            node = parent.get(node)

        path = []
        while not rev_stack.is_empty():
            path.append(rev_stack.pop())
        return len(path) - 1, path

    def people_you_may_know(self, username, limit=10):
        """Rank unconnected users by Jaccard Similarity using MaxHeap."""
        if not self.has_vertex(username):
            return []
        my_neighbors = self.adj_list.get(username)
        my_outgoing = self.outgoing_requests.get(username)
        heap = MaxHeap()

        for candidate in self.adj_list.keys():
            if candidate == username or my_neighbors.contains(candidate):
                continue
            if my_outgoing is not None and my_outgoing.contains(candidate):
                continue

            cand_neighbors = self.adj_list.get(candidate)
            mutuals = my_neighbors.intersection(cand_neighbors)
            mutual_count = len(mutuals)
            union_count = len(my_neighbors) + len(cand_neighbors) - mutual_count
            jaccard = (mutual_count / union_count) if union_count > 0 else 0.0

            if mutual_count > 0:
                heap.push((jaccard, mutual_count, candidate), {
                    "username": candidate,
                    "mutual_count": mutual_count,
                    "mutual_users": sorted(mutuals.to_list()),
                    "jaccard_score": round(jaccard, 4),
                })

        suggestions = []
        while not heap.is_empty() and len(suggestions) < limit:
            _, info = heap.pop_max()
            suggestions.append(info)
        return suggestions

    def detect_communities(self):
        """Detect connected student communities via Union-Find and MaxHeap."""
        dsu = DisjointSetUnion()
        all_users = self.adj_list.keys().to_list()
        for u in all_users:
            dsu.make_set(u)
            for v in self.adj_list.get(u):
                dsu.union(u, v)

        groups = HashTable()
        for u in all_users:
            root = dsu.find(u)
            members = groups.get(root)
            if members is None:
                members = DynamicArray()
                groups.put(root, members)
            members.append(u)

        heap = MaxHeap()
        for root in groups.keys():
            members_list = sorted(groups.get(root).to_list())
            internal_edges = sum(len(self.adj_list.get(m)) for m in members_list) // 2
            heap.push((len(members_list), internal_edges, root), {
                "community_id": root,
                "members": members_list,
                "size": len(members_list),
                "connections_count": internal_edges,
            })

        result = []
        while not heap.is_empty():
            _, comm = heap.pop_max()
            result.append(comm)
        return result


# ==============================================================================
# 6. CORE ENGINE & PERSISTENCE
# ==============================================================================
def hash_password(password, salt_hex=None):
    """Hash password with hashlib PBKDF2-HMAC-SHA256 and random 16-byte salt."""
    if salt_hex is None:
        salt_bytes = os.urandom(16)
        salt_hex = salt_bytes.hex()
    else:
        salt_bytes = bytes.fromhex(salt_hex)
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt_bytes, 100_000)
    return f"{salt_hex}${dk.hex()}"


def verify_password(password, stored_hash):
    if not stored_hash or "$" not in stored_hash:
        return False
    salt_hex, expected_hex = stored_hash.split("$", 1)
    computed = hash_password(password, salt_hex=salt_hex)
    return hmac.compare_digest(computed, f"{salt_hex}${expected_hex}")


class CloudStorageError(RuntimeError):
    pass


class SupabaseStore:
    """Server-only REST access to the single network_state row."""
    def __init__(self, url, key):
        if not re.fullmatch(r"https://[a-z0-9-]+\.supabase\.co/?", url):
            raise ValueError("Use the HTTPS Supabase project URL.")
        self.url = url.rstrip("/") + "/rest/v1/network_state"
        self.headers = {"apikey": key, "Content-Type": "application/json"}
        if not key.startswith("sb_secret_"):
            self.headers["Authorization"] = "Bearer " + key

    def request(self, method, query, payload=None):
        headers = dict(self.headers)
        headers["Prefer"] = "resolution=merge-duplicates,return=minimal"
        data = None if payload is None else json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(self.url + query, data=data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=30) as response:
                raw = response.read()
                return json.loads(raw) if raw else None
        except (OSError, ValueError) as exc:
            raise CloudStorageError("Supabase request failed; check configuration and connectivity.") from exc

    def load(self):
        rows = self.request("GET", "?id=eq.1&select=payload")
        return rows[0]["payload"] if rows else None

    def save(self, payload):
        self.request("POST", "?on_conflict=id", {"id": 1, "payload": payload})


class ChanakyaNetEngine:
    """Core in-memory DSA social networking engine with JSON persistence."""

    def __init__(self, data_dir=None):
        base_dir = os.path.dirname(os.path.abspath(__file__))
        self.data_dir = data_dir or os.path.join(base_dir, "chanakya_data")
        self.uploads_dir = os.path.join(self.data_dir, "uploads")
        self.db_path = os.path.join(self.data_dir, "network_data.json")
        self.registry_path = os.path.join(self.data_dir, "known_user_ids.json")
        self.known_ids = {}
        os.makedirs(self.data_dir, exist_ok=True)
        os.makedirs(self.uploads_dir, exist_ok=True)

        self.users = HashTable()
        self.sessions = HashTable()
        self.graph = SocialGraph()
        self.search_trie = Trie()
        self.posts_by_id = HashTable()
        self.posts_by_user = HashTable()
        self.notifications = HashTable()
        self.undo_stacks = HashTable()
        self.nav_stacks = HashTable()
        self.messages = HashTable()   # "userA|userB" (sorted) -> DynamicArray of message dicts

        url = os.environ.get("SUPABASE_URL", "").strip()
        key = os.environ.get("SUPABASE_SERVICE_KEY", "").strip()
        if bool(url) != bool(key) or (os.environ.get("RENDER") and not url):
            raise RuntimeError("Configure both Supabase environment variables.")
        self.cloud = SupabaseStore(url, key) if url else None
        self.storage_failed = False
        if self.cloud:
            payload = self.cloud.load()
            if payload is not None:
                self._load_from_disk(payload)
            else:
                self._save_to_disk()
        elif os.path.exists(self.db_path):
            self._load_from_disk()
        else:
            if os.environ.get("ENABLE_DEMO_DATA") == "1":
                self._seed_sample_data()
            self._save_to_disk()

        if not self.cloud:
            self._load_registry()
            self._sync_registry_with_users()

    # ---------------- Known user-ID registry ----------------
    # Every user ID typed into the Log In / Sign Up forms is remembered on disk
    # (known_user_ids.json). Passwords are never stored here - IDs only.
    _ID_RE = re.compile(r"^[a-z0-9_]{3,24}$")
    _MAX_UNREGISTERED_IDS = 2000

    def _load_registry(self):
        self.known_ids = {}
        if not os.path.exists(self.registry_path):
            return
        try:
            with open(self.registry_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            for rec in data.get("ids", []):
                uid = str(rec.get("id", "")).strip().lower()
                if self._ID_RE.match(uid):
                    self.known_ids[uid] = {
                        "first_seen": float(rec.get("first_seen", time.time())),
                        "last_seen": float(rec.get("last_seen", time.time())),
                        "logins": int(rec.get("logins", 0)),
                        "failed": int(rec.get("failed", 0)),
                        "signups": int(rec.get("signups", 0)),
                    }
        except (OSError, ValueError, TypeError, AttributeError):
            self.known_ids = {}

    def _save_registry(self):
        ids = [dict(id=uid, **rec) for uid, rec in self.known_ids.items()]
        ids.sort(key=lambda r: r["first_seen"])
        tmp_path = self.registry_path + ".tmp"
        try:
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump({"ids": ids}, f, indent=2)
            os.replace(tmp_path, self.registry_path)
        except OSError as exc:
            print(f"[ChanakyaConnect] Could not save user-ID registry: {exc}")

    def _sync_registry_with_users(self):
        changed = False
        for uid in self.users.keys():
            if uid not in self.known_ids:
                created = self.users.get(uid).get("created_at", time.time())
                self.known_ids[uid] = {"first_seen": created, "last_seen": created,
                                       "logins": 0, "failed": 0, "signups": 1}
                changed = True
        if changed or not os.path.exists(self.registry_path):
            self._save_registry()

    def _prune_registry(self):
        stale = [(rec["last_seen"], uid) for uid, rec in self.known_ids.items()
                 if not self.users.contains(uid)]
        excess = len(stale) - self._MAX_UNREGISTERED_IDS
        if excess > 0:
            stale.sort()
            for _, uid in stale[:excess]:
                del self.known_ids[uid]

    def record_user_id(self, username, event="seen"):
        """Remember a user ID typed into the UI. event: seen | login_ok | login_fail | signup_ok."""
        if self.cloud:
            return
        uid = username.strip().lower() if isinstance(username, str) else ""
        if not self._ID_RE.match(uid):
            return
        now = time.time()
        rec = self.known_ids.get(uid)
        if rec is None:
            rec = {"first_seen": now, "last_seen": now, "logins": 0, "failed": 0, "signups": 0}
            self.known_ids[uid] = rec
            self._prune_registry()
        rec["last_seen"] = now
        if event == "login_ok":
            rec["logins"] += 1
        elif event == "login_fail":
            rec["failed"] += 1
        elif event == "signup_ok":
            rec["signups"] += 1
        self._save_registry()

    def _index_user_in_trie(self, username, name):
        self.search_trie.insert(username, username)
        if name:
            self.search_trie.insert(name, username)
            for token in name.strip().split():
                self.search_trie.insert(token, username)

    def _deindex_user_in_trie(self, username, name):
        self.search_trie.remove(username, username)
        if name:
            self.search_trie.remove(name, username)
            for token in name.strip().split():
                self.search_trie.remove(token, username)

    def _ensure_user_containers(self, username):
        self.graph.add_vertex(username)
        if not self.posts_by_user.contains(username):
            self.posts_by_user.put(username, DynamicArray())
        if not self.notifications.contains(username):
            self.notifications.put(username, Queue())
        if not self.undo_stacks.contains(username):
            self.undo_stacks.put(username, Stack(max_size=30))
        if not self.nav_stacks.contains(username):
            self.nav_stacks.put(username, Stack(max_size=50))

    def _save_to_disk(self):
        users_list = [
            {
                "username": u["username"],
                "password_hash": u["password_hash"],
                "name": u["name"],
                "programme": u["programme"],
                "year": u["year"],
                "bio": u["bio"],
                "skills": u["skills"],
                "created_at": u["created_at"],
            }
            for u in self.users.values()
        ]
        edges = []
        for u in self.graph.adj_list.keys():
            for v in self.graph.adj_list.get(u):
                if u < v:
                    edges.append([u, v])

        pending_requests = []
        for receiver in self.graph.incoming_requests.keys():
            for req in self.graph.incoming_requests.get(receiver):
                pending_requests.append({
                    "from": req["from"],
                    "to": receiver,
                    "timestamp": req["timestamp"],
                })

        posts_list = [
            {
                "post_id": p["post_id"],
                "author": p["author"],
                "title": p["title"],
                "content": p["content"],
                "image_url": p["image_url"],
                "image_urls": self._post_images(p),
                "tags": p["tags"],
                "timestamp": p["timestamp"],
                "likes": p["likes"].to_list(),
                "comments": p["comments"].to_list(),
                "reactions": {em: rset.to_list() for em, rset in p.get("reactions", {}).items() if len(rset) > 0},
            }
            for p in self.posts_by_id.values()
        ]
        posts_list.sort(key=lambda item: item["timestamp"])

        notif_map = {}
        for uname in self.notifications.keys():
            q = self.notifications.get(uname)
            if len(q) > 0:
                notif_map[uname] = q.to_list()

        messages_list = []
        for conv_key in self.messages.keys():
            for m in self.messages.get(conv_key):
                messages_list.append(dict(m))
        messages_list.sort(key=lambda item: item["timestamp"])

        payload = {"users": users_list, "edges": edges,
                   "pending_requests": pending_requests, "posts": posts_list,
                   "notifications": notif_map, "messages": messages_list}
        if self.cloud:
            if self.storage_failed:
                raise CloudStorageError("Storage unavailable; restart required.")
            try:
                self.cloud.save(payload)
            except CloudStorageError:
                self.storage_failed = True
                raise
        else:
            tmp_path = self.db_path + ".tmp"
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump(payload, f, indent=2)
            os.replace(tmp_path, self.db_path)

    def _load_from_disk(self, payload=None):
        if payload is None:
            with open(self.db_path, "r", encoding="utf-8") as f:
                payload = json.load(f)

        for u in payload.get("users", []):
            uname = u["username"]
            self.users.put(uname, u)
            self._ensure_user_containers(uname)
            self._index_user_in_trie(uname, u.get("name", ""))

        for pair in payload.get("edges", []):
            if len(pair) == 2:
                self.graph.add_undirected_edge(pair[0], pair[1])

        for req in payload.get("pending_requests", []):
            s, r = req.get("from"), req.get("to")
            if self.users.contains(s) and self.users.contains(r):
                self.graph.send_request(s, r, req.get("timestamp", time.time()))

        for p in sorted(payload.get("posts", []), key=lambda item: item["timestamp"]):
            author = p["author"]
            if not self.users.contains(author):
                continue
            post_obj = {
                "post_id": p["post_id"],
                "author": author,
                "title": p.get("title", ""),
                "content": p.get("content", ""),
                "image_url": p.get("image_url", ""),
                "image_urls": self._post_images(p),
                "tags": p.get("tags", []),
                "timestamp": p["timestamp"],
                "likes": HashSet(p.get("likes", [])),
                "comments": CommentTree.from_list(p.get("comments", [])),
                "reactions": {em: HashSet(users) for em, users in p.get("reactions", {}).items()},
            }
            self.posts_by_id.put(post_obj["post_id"], post_obj)
            self.posts_by_user.get(author).append(post_obj)

        for m in payload.get("messages", []):
            sender, receiver = m.get("from"), m.get("to")
            if not (self.users.contains(sender) and self.users.contains(receiver)):
                continue
            key = self._conv_key(sender, receiver)
            if not self.messages.contains(key):
                self.messages.put(key, DynamicArray())
            self.messages.get(key).append({
                "msg_id": m.get("msg_id") or uuid.uuid4().hex[:12],
                "from": sender,
                "to": receiver,
                "text": str(m.get("text", "")),
                "timestamp": m.get("timestamp", time.time()),
                "read": bool(m.get("read", False)),
            })

        for uname, nlist in payload.get("notifications", {}).items():
            if self.notifications.contains(uname):
                q = self.notifications.get(uname)
                for n in nlist:
                    q.enqueue(n)

    def _public_user(self, user_dict):
        return {
            "username": user_dict["username"],
            "name": user_dict["name"],
            "programme": user_dict["programme"],
            "year": user_dict["year"],
            "bio": user_dict["bio"],
            "skills": list(user_dict["skills"]),
            "created_at": user_dict["created_at"],
            "connections_count": len(self.graph.get_connections(user_dict["username"])),
        }

    def signup(self, username, password, name, programme, year, bio="", skills=None):
        clean_user = (username or "").strip().lower()
        self.record_user_id(clean_user, "seen")
        if not re.match(r"^[a-z0-9_]{3,24}$", clean_user):
            return False, "Username must be 3-24 chars (letters, numbers, underscores).", None
        if self.users.contains(clean_user):
            return False, "Username already exists.", None
        if not password or len(password) < 8:
            return False, "Password must be at least 8 characters.", None
        clean_name = (name or "").strip()
        if not clean_name:
            return False, "Full name is required.", None

        skill_list = (
            [s.strip() for s in skills.split(",") if s.strip()]
            if isinstance(skills, str)
            else [str(s).strip() for s in (skills or []) if str(s).strip()]
        )
        user_record = {
            "username": clean_user,
            "password_hash": hash_password(password),
            "name": clean_name,
            "programme": (programme or "B.Tech. CSE").strip(),
            "year": (year or "II Year").strip(),
            "bio": (bio or "").strip(),
            "skills": skill_list,
            "created_at": time.time(),
        }
        self.users.put(clean_user, user_record)
        self._ensure_user_containers(clean_user)
        self._index_user_in_trie(clean_user, clean_name)

        token = uuid.uuid4().hex
        self.sessions.put(token, clean_user)
        self._save_to_disk()
        self.record_user_id(clean_user, "signup_ok")
        return True, "Account created.", {"token": token, "user": self._public_user(user_record)}

    def login(self, username, password):
        clean_user = (username or "").strip().lower()
        user_record = self.users.get(clean_user)
        if user_record is None or not verify_password(password or "", user_record["password_hash"]):
            self.record_user_id(clean_user, "login_fail")
            return False, "Invalid username or password.", None
        token = uuid.uuid4().hex
        self.sessions.put(token, clean_user)
        self.record_user_id(clean_user, "login_ok")
        return True, "Logged in.", {"token": token, "user": self._public_user(user_record)}

    def logout(self, token):
        if token:
            self.sessions.remove(token)

    def get_session_user(self, token):
        return self.sessions.get(token) if token else None

    def update_profile(self, username, name, programme, year, bio, skills):
        user_record = self.users.get(username)
        if user_record is None:
            return False, "User not found.", None
        old_name = user_record["name"]
        new_name = (name or old_name).strip()
        if new_name != old_name:
            self._deindex_user_in_trie(username, old_name)
            self._index_user_in_trie(username, new_name)

        skill_list = (
            [s.strip() for s in skills.split(",") if s.strip()]
            if isinstance(skills, str)
            else user_record["skills"]
        )
        user_record["name"] = new_name
        user_record["programme"] = (programme or user_record["programme"]).strip()
        user_record["year"] = (year or user_record["year"]).strip()
        user_record["bio"] = (bio if bio is not None else user_record["bio"]).strip()
        user_record["skills"] = skill_list
        self._save_to_disk()
        return True, "Profile updated.", self._public_user(user_record)

    def get_profile(self, viewer_username, target_username):
        clean_target = (target_username or "").strip().lower()
        target_user = self.users.get(clean_target)
        if target_user is None:
            return False, "User not found.", None

        status = "none"
        if viewer_username == clean_target:
            status = "self"
        elif self.graph.are_connected(viewer_username, clean_target):
            status = "connected"
        elif self.graph.has_pending_request(viewer_username, clean_target):
            status = "outgoing_pending"
        elif self.graph.has_pending_request(clean_target, viewer_username):
            status = "incoming_pending"

        mutuals = (
            sorted(self.graph.get_mutual_connections(viewer_username, clean_target))
            if viewer_username != clean_target
            else []
        )
        degree, path = self.graph.bfs_shortest_path(viewer_username, clean_target)
        return True, "Profile loaded.", {
            "user": self._public_user(target_user),
            "connection_status": status,
            "mutual_connections": [
                {"username": m, "name": self.users.get(m)["name"], "programme": self.users.get(m)["programme"]}
                for m in mutuals
            ],
            "degree": degree,
            "shortest_chain": [{"username": u, "name": self.users.get(u)["name"]} for u in path],
            "posts": self.get_user_posts(clean_target, viewer_username),
            "connections": [
                self._public_user(self.users.get(c))
                for c in sorted(self.graph.get_connections(clean_target))
            ],
        }

    def _push_notification(self, target_username, ntype, actor_username, message, ref_id=None):
        if not self.notifications.contains(target_username):
            return
        actor = self.users.get(actor_username)
        self.notifications.get(target_username).enqueue({
            "notif_id": uuid.uuid4().hex[:10],
            "type": ntype,
            "actor": actor_username,
            "actor_name": actor["name"] if actor else actor_username,
            "message": message,
            "ref_id": ref_id,
            "timestamp": time.time(),
        })

    def send_connection_request(self, sender, receiver):
        clean_recv = (receiver or "").strip().lower()
        ok, msg = self.graph.send_request(sender, clean_recv, time.time())
        if ok:
            if self.graph.are_connected(sender, clean_recv):
                self._push_notification(clean_recv, "connection_accepted", sender, "accepted your request (mutual!).")
            else:
                self._push_notification(clean_recv, "connection_request", sender, "sent you a connection request.")
            self._save_to_disk()
        return ok, msg

    def accept_connection_request(self, receiver, sender):
        clean_sender = (sender or "").strip().lower()
        ok, msg = self.graph.accept_request(clean_sender, receiver)
        if ok:
            self._push_notification(clean_sender, "connection_accepted", receiver, "accepted your connection request.")
            self._save_to_disk()
        return ok, msg

    def reject_connection_request(self, receiver, sender):
        clean_sender = (sender or "").strip().lower()
        ok, msg = self.graph.reject_request(clean_sender, receiver)
        if ok:
            self.undo_stacks.get(receiver).push({
                "action": "reject_request",
                "label": f"Reject request from @{clean_sender}",
                "sender": clean_sender,
                "receiver": receiver,
                "timestamp": time.time(),
            })
            self._save_to_disk()
        return ok, msg

    def cancel_connection_request(self, sender, receiver):
        ok, msg = self.graph.cancel_request(sender, (receiver or "").strip().lower())
        if ok:
            self._save_to_disk()
        return ok, msg

    def remove_connection(self, username, target_username):
        clean_target = (target_username or "").strip().lower()
        ok, msg = self.graph.remove_connection(username, clean_target)
        if ok:
            self.undo_stacks.get(username).push({
                "action": "remove_connection",
                "label": f"Remove connection @{clean_target}",
                "u": username,
                "v": clean_target,
            })
            self._save_to_disk()
        return ok, msg

    def get_network_overview(self, username):
        my_conns = []
        for c in sorted(self.graph.get_connections(username)):
            info = self._public_user(self.users.get(c))
            info["mutual_count"] = len(self.graph.get_mutual_connections(username, c))
            my_conns.append(info)

        incoming = []
        for req in self.graph.incoming_requests.get(username):
            su = self.users.get(req["from"])
            if su:
                incoming.append({
                    "user": self._public_user(su),
                    "timestamp": req["timestamp"],
                    "mutual_count": len(self.graph.get_mutual_connections(username, req["from"])),
                })

        outgoing = [
            self._public_user(self.users.get(t))
            for t in sorted(self.graph.outgoing_requests.get(username).to_list())
            if self.users.get(t)
        ]

        suggestions = []
        seen = HashSet()
        for item in self.graph.people_you_may_know(username, limit=12):
            cand = item["username"]
            seen.add(cand)
            suggestions.append({
                "user": self._public_user(self.users.get(cand)),
                "mutual_count": item["mutual_count"],
                "jaccard_score": item["jaccard_score"],
            })

        if len(suggestions) < 6:
            my_neighbors = self.graph.adj_list.get(username)
            my_out = self.graph.outgoing_requests.get(username)
            my_in = HashSet([r["from"] for r in self.graph.incoming_requests.get(username)])
            for cand in sorted(self.users.keys().to_list()):
                if len(suggestions) >= 8:
                    break
                if cand == username or my_neighbors.contains(cand) or my_out.contains(cand) or my_in.contains(cand) or seen.contains(cand):
                    continue
                suggestions.append({
                    "user": self._public_user(self.users.get(cand)),
                    "mutual_count": 0,
                    "jaccard_score": 0.0,
                })

        return {
            "connections": my_conns,
            "incoming_requests": incoming,
            "outgoing_requests": outgoing,
            "people_you_may_know": suggestions,
        }

    def get_communities(self):
        communities = []
        for idx, comm in enumerate(self.graph.detect_communities(), start=1):
            members = [self._public_user(self.users.get(m)) for m in comm["members"]]
            skill_counts = HashTable()
            for m in members:
                for sk in m["skills"]:
                    skill_counts.put(sk, skill_counts.get(sk, 0) + 1)
            skill_heap = MaxHeap()
            for sk, cnt in skill_counts.items():
                skill_heap.push((cnt, sk), sk)
            top_skills = []
            while not skill_heap.is_empty() and len(top_skills) < 4:
                top_skills.append(skill_heap.pop_max()[1])
            communities.append({
                "id": idx,
                "name": f"Cluster #{idx}" + (f" ({top_skills[0]} & Peers)" if top_skills else ""),
                "size": comm["size"],
                "connections_count": comm["connections_count"],
                "top_skills": top_skills,
                "members": members,
            })
        return communities

    def _serialize_post(self, post_obj, viewer_username):
        author_dict = self.users.get(post_obj["author"])
        # Build reactions dict: emoji -> count
        reactions_raw = post_obj.get("reactions", {})
        reactions_out = {}
        my_reactions = []
        for em, users_set in reactions_raw.items():
            count = len(users_set)
            if count > 0:
                reactions_out[em] = count
            if viewer_username and users_set.contains(viewer_username):
                my_reactions.append(em)
        return {
            "post_id": post_obj["post_id"],
            "author": post_obj["author"],
            "author_name": author_dict["name"] if author_dict else post_obj["author"],
            "author_programme": author_dict["programme"] if author_dict else "",
            "author_year": author_dict["year"] if author_dict else "",
            "title": post_obj["title"],
            "content": post_obj["content"],
            "image_url": post_obj["image_url"],
            "image_urls": self._post_images(post_obj),
            "tags": list(post_obj["tags"]),
            "timestamp": post_obj["timestamp"],
            "likes_count": len(post_obj["likes"]),
            "liked_by_me": post_obj["likes"].contains(viewer_username) if viewer_username else False,
            "comments_count": post_obj["comments"].count_all(),
            "comments": post_obj["comments"].to_list(),
            "reactions": reactions_out,
            "my_reactions": my_reactions,
        }

    def _save_base64_image(self, image_data_url):
        if not image_data_url:
            return ""
        if self.cloud and image_data_url.startswith(("http://", "https://", "/uploads/")):
            raise ValueError("Upload an image file instead of an external URL.")
        if image_data_url.startswith(("http://", "https://", "/uploads/")):
            return image_data_url
        match = re.match(r"^data:image/(png|jpeg|jpg|gif|webp);base64,(.+)$", image_data_url, re.IGNORECASE | re.DOTALL)
        if not match:
            raise ValueError("Unsupported image format.")
        ext = "jpg" if match.group(1).lower() == "jpeg" else match.group(1).lower()
        raw = base64.b64decode(match.group(2), validate=True)
        if len(raw) > 5 * 1024 * 1024:
            raise ValueError("Image size must be 5 MB or less.")
        if self.cloud:
            if len(raw) > 256 * 1024:
                raise ValueError("Cloud demo images must be 256 KB or less.")
            return "data:image/" + ext.replace("jpg", "jpeg") + ";base64," + base64.b64encode(raw).decode("ascii")
        fname = f"post_{uuid.uuid4().hex[:12]}.{ext}"
        with open(os.path.join(self.uploads_dir, fname), "wb") as f:
            f.write(raw)
        return f"/uploads/{fname}"

    @staticmethod
    def _post_images(post):
        """All image URLs of a post (supports old single-image posts too)."""
        urls = post.get("image_urls")
        if urls:
            return [u for u in urls if u]
        single = post.get("image_url")
        return [single] if single else []

    MAX_IMAGES_PER_POST = 10

    def create_post(self, author, content, title="", image_data="", tags=None, images=None):
        clean_content = (content or "").strip()
        clean_title = (title or "").strip()
        raw_images = [x for x in (images or []) if isinstance(x, str) and x]
        if image_data and not raw_images:
            raw_images = [image_data]
        if len(raw_images) > self.MAX_IMAGES_PER_POST:
            return False, f"You can attach up to {self.MAX_IMAGES_PER_POST} images per post.", None
        if not clean_content and not raw_images:
            return False, "Post cannot be empty.", None
        try:
            image_urls = [u for u in (self._save_base64_image(x) for x in raw_images) if u]
        except ValueError as exc:
            return False, str(exc), None

        tag_list = (
            [t.strip().lstrip("#") for t in tags.split(",") if t.strip()]
            if isinstance(tags, str)
            else [str(t).strip().lstrip("#") for t in (tags or []) if str(t).strip()]
        )
        post_obj = {
            "post_id": f"p_{uuid.uuid4().hex[:10]}",
            "author": author,
            "title": clean_title,
            "content": clean_content,
            "image_url": image_urls[0] if image_urls else "",
            "image_urls": image_urls,
            "tags": tag_list,
            "timestamp": time.time(),
            "likes": HashSet(),
            "comments": CommentTree(),
            "reactions": {},
        }
        self.posts_by_id.put(post_obj["post_id"], post_obj)
        self.posts_by_user.get(author).append(post_obj)
        self._save_to_disk()
        return True, "Post published.", self._serialize_post(post_obj, author)

    def delete_post(self, username, post_id):
        post_obj = self.posts_by_id.get(post_id)
        if post_obj is None:
            return False, "Post not found."
        if post_obj["author"] != username:
            return False, "You can only delete your own posts."

        self.undo_stacks.get(username).push({
            "action": "delete_post",
            "label": f"Delete post '{post_obj['title'] or post_obj['content'][:24]}'",
            "post_snapshot": {
                "post_id": post_obj["post_id"],
                "author": post_obj["author"],
                "title": post_obj["title"],
                "content": post_obj["content"],
                "image_url": post_obj["image_url"],
                "image_urls": self._post_images(post_obj),
                "tags": list(post_obj["tags"]),
                "timestamp": post_obj["timestamp"],
                "likes": post_obj["likes"].to_list(),
                "comments": post_obj["comments"].to_list(),
            },
        })
        self.posts_by_id.remove(post_id)
        arr = self.posts_by_user.get(username)
        for i in range(len(arr)):
            if arr[i]["post_id"] == post_id:
                arr.pop(i)
                break
        self._save_to_disk()
        return True, "Post deleted (Undo available)."

    def get_user_posts(self, target_username, viewer_username):
        arr = self.posts_by_user.get(target_username)
        if arr is None:
            return []
        return [self._serialize_post(arr[i], viewer_username) for i in range(len(arr) - 1, -1, -1)]

    def get_home_feed(self, username, include_own=False, limit=50):
        """K-way merge of connections' time-ordered DynamicArrays using MaxHeap."""
        sources = self.graph.get_connections(username)
        if include_own and username not in sources:
            sources.append(username)

        heap = MaxHeap()
        for src in sources:
            arr = self.posts_by_user.get(src)
            if arr is not None and len(arr) > 0:
                idx = len(arr) - 1
                p = arr[idx]
                heap.push((p["timestamp"], p["post_id"]), (src, idx))

        feed = []
        while not heap.is_empty() and len(feed) < limit:
            _, (src, idx) = heap.pop_max()
            arr = self.posts_by_user.get(src)
            feed.append(self._serialize_post(arr[idx], username))
            if idx - 1 >= 0:
                prev_p = arr[idx - 1]
                heap.push((prev_p["timestamp"], prev_p["post_id"]), (src, idx - 1))
        return feed

    def get_trending_posts(self, username, limit=10):
        sources = self.graph.get_connections(username)
        if username not in sources:
            sources.append(username)
        heap = MaxHeap()
        for src in sources:
            arr = self.posts_by_user.get(src)
            if arr is None:
                continue
            for p in arr:
                score = len(p["likes"]) + 2 * p["comments"].count_all()
                if score > 0:
                    heap.push((score, p["timestamp"], p["post_id"]), p)
        trending = []
        while not heap.is_empty() and len(trending) < limit:
            (score, _, _), p = heap.pop_max()
            item = self._serialize_post(p, username)
            item["trend_score"] = score
            trending.append(item)
        return trending

    def toggle_reaction(self, username, post_id, emoji):
        allowed = {"👍", "🔥", "🎉", "💡", "🤝"}
        if emoji not in allowed:
            return False, "Invalid emoji.", None
        post_obj = self.posts_by_id.get(post_id)
        if post_obj is None:
            return False, "Post not found.", None
        if "reactions" not in post_obj:
            post_obj["reactions"] = {}
        if emoji not in post_obj["reactions"]:
            post_obj["reactions"][emoji] = HashSet()
        rset = post_obj["reactions"][emoji]
        if rset.contains(username):
            rset.remove(username)
        else:
            rset.add(username)
        self._save_to_disk()
        return True, "Reaction updated.", self._serialize_post(post_obj, username)

    def toggle_like(self, username, post_id):
        post_obj = self.posts_by_id.get(post_id)
        if post_obj is None:
            return False, "Post not found.", None
        likes_set = post_obj["likes"]
        if likes_set.contains(username):
            likes_set.remove(username)
            liked = False
        else:
            likes_set.add(username)
            liked = True
            if post_obj["author"] != username:
                label = post_obj["title"] or post_obj["content"][:30]
                self._push_notification(post_obj["author"], "like", username, f'liked your post "{label}".', post_id)
        self._save_to_disk()
        return True, "Updated.", {"liked": liked, "likes_count": len(likes_set)}

    def add_comment(self, username, post_id, text, parent_comment_id=None):
        post_obj = self.posts_by_id.get(post_id)
        if post_obj is None:
            return False, "Post not found.", None
        clean = (text or "").strip()
        if not clean:
            return False, "Comment cannot be empty.", None
        node = post_obj["comments"].add_comment(f"c_{uuid.uuid4().hex[:10]}", username, clean, time.time(), parent_comment_id or None)
        if node is None:
            return False, "Parent comment not found.", None
        if parent_comment_id:
            parent_node = post_obj["comments"].find_comment(parent_comment_id)
            if parent_node and parent_node.author != username:
                self._push_notification(parent_node.author, "reply", username, f'replied: "{clean[:30]}"', post_id)
        if post_obj["author"] != username:
            self._push_notification(post_obj["author"], "comment", username, f'commented: "{clean[:30]}"', post_id)
        self._save_to_disk()
        return True, "Comment added.", self._serialize_post(post_obj, username)

    def search_users(self, query, viewer_username=None, limit=10):
        results = []
        for uname in self.search_trie.search_prefix(query, limit=limit):
            u = self.users.get(uname)
            if not u:
                continue
            item = self._public_user(u)
            if viewer_username:
                item["is_self"] = (viewer_username == uname)
                deg, _ = self.graph.bfs_shortest_path(viewer_username, uname)
                item["degree"] = deg
            results.append(item)
        return results

    def undo_last_action(self, username):
        stack = self.undo_stacks.get(username)
        if stack is None or stack.is_empty():
            return False, "Nothing to undo."
        entry = stack.pop()
        action = entry["action"]
        if action == "delete_post":
            snap = entry["post_snapshot"]
            restored = {
                "post_id": snap["post_id"],
                "author": snap["author"],
                "title": snap["title"],
                "content": snap["content"],
                "image_url": snap["image_url"],
                "image_urls": self._post_images(snap),
                "tags": list(snap["tags"]),
                "timestamp": snap["timestamp"],
                "likes": HashSet(snap["likes"]),
                "comments": CommentTree.from_list(snap["comments"]),
            }
            self.posts_by_id.put(restored["post_id"], restored)
            arr = self.posts_by_user.get(username)
            arr.append(restored)
            sorted_posts = sorted(arr.to_list(), key=lambda p: p["timestamp"])
            arr.clear()
            for p in sorted_posts:
                arr.append(p)
            self._save_to_disk()
            return True, f"Undid: {entry['label']}"
        if action == "remove_connection":
            self.graph.add_undirected_edge(entry["u"], entry["v"])
            self._save_to_disk()
            return True, f"Undid: {entry['label']}"
        if action == "reject_request":
            self.graph.send_request(entry["sender"], entry["receiver"], entry["timestamp"])
            self._save_to_disk()
            return True, f"Undid: {entry['label']}"
        return False, "Unknown undo entry."

    def get_undo_peek(self, username):
        stack = self.undo_stacks.get(username)
        if stack is None or stack.is_empty():
            return None
        return {"label": stack.peek()["label"], "count": len(stack)}

    def push_navigation(self, username, view, target=None):
        stack = self.nav_stacks.get(username)
        if stack is None:
            return []
        item = {"view": view, "target": target}
        if stack.peek() != item:
            stack.push(item)
        return stack.to_list()

    def pop_navigation(self, username):
        stack = self.nav_stacks.get(username)
        if stack is None or len(stack) <= 1:
            return None, stack.to_list() if stack else []
        stack.pop()
        return stack.peek(), stack.to_list()

    def get_notifications(self, username):
        q = self.notifications.get(username)
        return [] if q is None else q.to_list()

    def clear_notifications(self, username):
        q = self.notifications.get(username)
        if q is not None:
            q.clear()
            self._save_to_disk()

    # ---------------- Direct messages (connected users only) ----------------
    MAX_MESSAGE_LEN = 1000

    @staticmethod
    def _conv_key(a, b):
        x, y = sorted([a, b])
        return f"{x}|{y}"

    @staticmethod
    def _public_message(m):
        return {"msg_id": m["msg_id"], "from": m["from"], "to": m["to"],
                "text": m["text"], "timestamp": m["timestamp"], "read": m["read"]}

    def send_message(self, sender, receiver, text):
        target = (receiver or "").strip().lower()
        clean = (text or "").strip() if isinstance(text, str) else ""
        if target == sender or not self.users.contains(target):
            return False, "User not found.", None
        if not self.graph.are_connected(sender, target):
            return False, "You can only message people you are connected with.", None
        if not clean:
            return False, "Message cannot be empty.", None
        if len(clean) > self.MAX_MESSAGE_LEN:
            return False, f"Message is too long (max {self.MAX_MESSAGE_LEN} characters).", None
        key = self._conv_key(sender, target)
        if not self.messages.contains(key):
            self.messages.put(key, DynamicArray())
        msg = {
            "msg_id": uuid.uuid4().hex[:12],
            "from": sender,
            "to": target,
            "text": clean,
            "timestamp": time.time(),
            "read": False,
        }
        self.messages.get(key).append(msg)
        self._save_to_disk()
        return True, "Message sent.", self._public_message(msg)

    def get_conversation(self, viewer, other):
        target = (other or "").strip().lower()
        user = self.users.get(target)
        if user is None or target == viewer:
            return False, "User not found.", None
        arr = self.messages.get(self._conv_key(viewer, target))
        out, changed = [], False
        if arr is not None:
            for m in arr:
                if m["to"] == viewer and not m["read"]:
                    m["read"] = True
                    changed = True
                out.append(self._public_message(m))
        if changed:
            self._save_to_disk()
        return True, "", {
            "user": {"username": target, "name": user["name"]},
            "messages": out[-300:],
            "can_message": self.graph.are_connected(viewer, target),
        }

    def get_inbox(self, viewer):
        convs = {}
        for u in self.graph.get_connections(viewer):
            convs[u] = {"last": None, "unread": 0}
        for key in self.messages.keys():
            a, b = key.split("|", 1)
            if viewer not in (a, b):
                continue
            other = b if a == viewer else a
            info = convs.setdefault(other, {"last": None, "unread": 0})
            for m in self.messages.get(key):
                info["last"] = m
                if m["to"] == viewer and not m["read"]:
                    info["unread"] += 1
        items = []
        for other, info in convs.items():
            user = self.users.get(other)
            if user is None:
                continue
            last = info["last"]
            items.append({
                "username": other,
                "name": user["name"],
                "connected": self.graph.are_connected(viewer, other),
                "unread": info["unread"],
                "last_text": last["text"][:80] if last else "",
                "last_ts": last["timestamp"] if last else 0,
                "last_from_me": bool(last and last["from"] == viewer),
            })
        items.sort(key=lambda r: r["name"].lower())
        items.sort(key=lambda r: r["last_ts"], reverse=True)
        return items

    def get_unread_total(self, username):
        total = 0
        for key in self.messages.keys():
            a, b = key.split("|", 1)
            if username in (a, b):
                total += sum(1 for m in self.messages.get(key) if m["to"] == username and not m["read"])
        return total

    def _seed_sample_data(self):
        sample_users = [
            ("aarav", "pass123", "Aarav Sharma", "B.Tech. CSE (AI & ML)", "III Year",
             "Building graph ML pipelines and open-source compilers at Chanakya.", ["Python", "Graphs", "PyTorch"]),
            ("diya", "pass123", "Diya Nair", "B.Tech. CSE", "III Year",
             "Full-stack builder exploring distributed systems and Trie search.", ["Python", "Algorithms", "Web"]),
            ("rohan", "pass123", "Rohan Kulkarni", "B.Tech. ECE", "III Year",
             "Embedded IoT + robotics lead. Love building autonomous rovers.", ["Embedded C", "ROS", "Python"]),
            ("sneha", "pass123", "Sneha Reddy", "B.Tech. CSE (Data Science)", "II Year",
             "Competitive programmer and data visualization enthusiast.", ["DSA", "Python", "Heaps"]),
            ("kabir", "pass123", "Kabir Mehta", "B.Tech. CSE", "IV Year",
             "Systems engineering intern. Mentoring juniors in DSA & backend.", ["Rust", "Go", "Trees"]),
            ("meera", "pass123", "Meera Joshi", "B.Tech. AI & Robotics", "II Year",
             "Computer vision projects and campus hackathon organizer.", ["OpenCV", "Python", "Robotics"]),
            ("vikram", "pass123", "Vikram Rao", "B.Tech. Mechanical", "III Year",
             "CAD modeling, FEA simulation, and solar EV team member.", ["SolidWorks", "MATLAB", "EV"]),
            ("ananya", "pass123", "Ananya Iyer", "B.Tech. CSE", "I Year",
             "First-year coder learning stacks, queues, and web dev.", ["Python", "HTML/CSS", "C"]),
        ]
        now = time.time()
        for idx, (uname, pwd, name, prog, yr, bio, skills) in enumerate(sample_users):
            self.users.put(uname, {
                "username": uname,
                "password_hash": hash_password(pwd),
                "name": name,
                "programme": prog,
                "year": yr,
                "bio": bio,
                "skills": skills,
                "created_at": now - (10 - idx) * 86400,
            })
            self._ensure_user_containers(uname)
            self._index_user_in_trie(uname, name)

        for u, v in [("aarav", "diya"), ("aarav", "rohan"), ("aarav", "sneha"),
                     ("diya", "kabir"), ("diya", "sneha"), ("rohan", "meera"),
                     ("meera", "vikram"), ("kabir", "ananya")]:
            self.graph.add_undirected_edge(u, v)

        self.graph.send_request("meera", "aarav", now - 1800)
        self.graph.send_request("vikram", "aarav", now - 900)
        self._push_notification("aarav", "connection_request", "meera", "sent you a connection request.")
        self._push_notification("aarav", "connection_request", "vikram", "sent you a connection request.")

        seed_posts = [
            ("diya", "Prefix Trie Autocomplete Benchmark",
             "Benchmarked our custom Trie vs linear scan for 5,000 Chanakya student names. Prefix lookup stayed under 0.2ms!",
             ["DSA", "Trie", "Python"], now - 14400, ["aarav", "sneha", "kabir"]),
            ("rohan", "Autonomous Rover Pathfinding Demo",
             "Integrated BFS grid obstacle avoidance on our campus rover prototype. Looking for CSE teammates!",
             ["Robotics", "BFS", "IoT"], now - 10800, ["aarav", "meera"]),
            ("sneha", "K-Way Heap Merge Cheat Sheet",
             "Instead of sorting all posts globally on every refresh, merging K sorted user timelines with a MaxHeap takes O(N log K).",
             ["Heaps", "Algorithms"], now - 7200, ["aarav", "diya"]),
            ("kabir", "Campus Coding Club Mock Interview",
             "Hosting a DSA mock interview session this Friday at Chanakya Block B: Graphs, Trees, and Stacks!",
             ["Mentorship", "DSA"], now - 5400, ["diya", "ananya"]),
            ("aarav", "Graph Neural Networks Study Group",
             "Starting a weekend study group on G(V, E) message passing and BFS/DFS embeddings. Comment to join!",
             ["AI", "Graphs"], now - 3600, ["diya", "rohan", "sneha"]),
        ]
        for author, title, content, tags, ts, likers in seed_posts:
            p = {
                "post_id": f"p_{uuid.uuid4().hex[:10]}",
                "author": author,
                "title": title,
                "content": content,
                "image_url": "",
                "tags": tags,
                "timestamp": ts,
                "likes": HashSet(likers),
                "comments": CommentTree(),
            }
            self.posts_by_id.put(p["post_id"], p)
            self.posts_by_user.get(author).append(p)
            if author == "diya":
                c1 = p["comments"].add_comment(f"c_{uuid.uuid4().hex[:8]}", "aarav", "Did you use HashTable inside each TrieNode?", ts + 120)
                p["comments"].add_comment(f"c_{uuid.uuid4().hex[:8]}", "diya", "Yes! Separate-chaining HashTable for children.", ts + 240, c1.comment_id)


# ==============================================================================
# 7. EMBEDDED SINGLE-PAGE WEBSITE (HTML + CSS + JS)
# ==============================================================================
HTML_PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8" />
<meta name="viewport" content="width=device-width, initial-scale=1.0" />
<title>ChanakyaConnect — Student DSA Network</title>
<style>
:root{--bg:#f1f5f9;--surface:#fff;--alt:#f8fafc;--border:#e2e8f0;--text:#0f172a;--muted:#64748b;--primary:#3730a3;--primary-h:#312e81;--soft:#eef2ff;--danger:#dc2626;--radius:12px;--shadow:0 2px 10px rgba(15,23,42,.06)}
*{box-sizing:border-box}
body{margin:0;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;background:var(--bg);color:var(--text);line-height:1.5}
.hidden{display:none!important}
.gallery{display:grid;gap:6px;margin:10px 0}.gallery.n1{grid-template-columns:1fr}.gallery.n2,.gallery.n4{grid-template-columns:1fr 1fr}.gallery.n3,.gallery.many{grid-template-columns:repeat(3,1fr)}
.gallery img{width:100%;height:100%;max-height:360px;object-fit:cover;border-radius:10px;border:1px solid var(--border);cursor:pointer}
.gallery.n2 img,.gallery.n4 img{height:220px}.gallery.n3 img,.gallery.many img{height:180px}
.preview-row{display:flex;flex-wrap:wrap;gap:8px;margin:0 0 10px}.preview-item{position:relative}
.preview-item img{width:72px;height:72px;object-fit:cover;border-radius:8px;border:1px solid var(--border)}
.preview-item button{position:absolute;top:-6px;right:-6px;width:20px;height:20px;border-radius:50%;border:none;background:#ef4444;color:#fff;cursor:pointer;line-height:1;font-size:13px;padding:0}
.chat-layout{display:grid;grid-template-columns:280px 1fr;gap:16px;align-items:start}
.chat-list{padding:8px;max-height:560px;overflow-y:auto}
.chat-item{display:flex;justify-content:space-between;align-items:center;gap:8px;padding:10px;border-radius:10px;cursor:pointer}
.chat-item:hover,.chat-item.active{background:var(--soft)}
.chat-item .meta{min-width:0}.chat-item .meta div{white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:180px}
.chat-pane{display:flex;flex-direction:column;height:560px;padding:0;overflow:hidden}
.chat-header{padding:14px 18px;border-bottom:1px solid var(--border);font-weight:600}
.chat-messages{flex:1;overflow-y:auto;padding:14px 18px;display:flex;flex-direction:column;gap:8px;background:var(--alt)}
.bubble{max-width:70%;padding:8px 12px;border-radius:14px;font-size:.92rem;word-wrap:break-word;white-space:pre-wrap}
.bubble.me{align-self:flex-end;background:var(--primary);color:#fff;border-bottom-right-radius:4px}
.bubble.them{align-self:flex-start;background:#fff;border:1px solid var(--border);border-bottom-left-radius:4px}
.bubble small{display:block;opacity:.7;font-size:.7rem;margin-top:3px}
.chat-form{display:flex;gap:8px;padding:12px;border-top:1px solid var(--border);background:#fff}.chat-form input{margin:0;flex:1}
@media(max-width:800px){.chat-layout{grid-template-columns:1fr}}
.muted{color:var(--muted);font-size:.88rem}
.toast{position:fixed;bottom:20px;right:20px;background:#0f172a;color:#fff;padding:12px 18px;border-radius:10px;box-shadow:0 8px 24px rgba(0,0,0,.22);z-index:9999;font-size:.9rem}
.toast.error{background:var(--danger)}
input,textarea,select{width:100%;padding:10px 12px;border:1px solid var(--border);border-radius:8px;font:inherit;background:#fff;margin-bottom:10px}
input:focus,textarea:focus,select:focus{outline:2px solid #c7d2fe;border-color:var(--primary)}
.btn{display:inline-flex;align-items:center;justify-content:center;gap:6px;padding:9px 14px;border-radius:8px;border:1px solid transparent;font:inherit;font-weight:600;font-size:.88rem;cursor:pointer}
.btn-sm{padding:6px 11px;font-size:.82rem}
.btn-primary{background:var(--primary);color:#fff}.btn-primary:hover{background:var(--primary-h)}
.btn-outline{background:#fff;border-color:var(--border);color:var(--text)}.btn-outline:hover{background:var(--alt)}
.btn-ghost{background:transparent;color:var(--text)}.btn-ghost:hover{background:var(--alt)}
.btn-danger-outline{background:#fff;border-color:#fecaca;color:var(--danger)}.btn-danger-outline:hover{background:#fef2f2}
.link-btn{background:none;border:none;color:var(--primary);cursor:pointer;font-weight:600;font-size:.84rem;padding:0}
.full-width{width:100%}.grid-2{display:grid;grid-template-columns:1fr 1fr;gap:10px}
/* Remove blue focus outline on avatars and icon buttons */
.avatar-lg:focus,.avatar-sm:focus,button:focus{outline:none;box-shadow:none}
.auth-screen{min-height:100vh;display:flex;align-items:center;justify-content:center;padding:24px;background:linear-gradient(135deg,#1e1b4b 0%,#312e81 45%,#0f172a 100%)}
.auth-card{width:100%;max-width:480px;background:#fff;border-radius:16px;padding:28px;box-shadow:0 20px 50px rgba(0,0,0,.3)}
.auth-brand{display:flex;align-items:center;gap:14px;margin-bottom:18px}
.auth-brand h1{margin:0;font-size:1.38rem}.auth-brand .subtitle{margin:2px 0 0;font-size:.82rem;color:var(--muted)}
.logo-badge{width:46px;height:46px;border-radius:12px;background:var(--primary);color:#fff;font-weight:800;display:flex;align-items:center;justify-content:center;flex-shrink:0}
.logo-badge.sm{width:32px;height:32px;font-size:.84rem;border-radius:8px}
.auth-tabs{display:grid;grid-template-columns:1fr 1fr;background:var(--alt);padding:4px;border-radius:10px;margin-bottom:16px}
.auth-tab{border:none;background:transparent;padding:9px;border-radius:8px;font-weight:600;cursor:pointer}
.auth-tab.active{background:#fff;color:var(--primary);box-shadow:var(--shadow)}
.auth-form label{display:block;font-size:.82rem;font-weight:600;margin-bottom:4px;color:#334155}
.navbar{position:sticky;top:0;z-index:100;background:#fff;border-bottom:1px solid var(--border);padding:10px 22px;display:flex;align-items:center;justify-content:space-between;gap:14px}
.nav-left,.nav-right{display:flex;align-items:center;gap:8px}
.nav-brand{display:flex;align-items:center;gap:8px;font-weight:800;font-size:1.05rem;cursor:pointer;color:var(--primary)}
.search-wrapper{position:relative;flex:1;max-width:430px}.search-wrapper input{margin-bottom:0;background:var(--alt)}
.search-dropdown{position:absolute;top:calc(100% + 6px);left:0;right:0;background:#fff;border:1px solid var(--border);border-radius:10px;box-shadow:0 12px 28px rgba(15,23,42,.14);z-index:200;max-height:320px;overflow-y:auto}
.search-item{padding:10px 14px;display:flex;align-items:center;justify-content:space-between;cursor:pointer;border-bottom:1px solid var(--alt)}
.search-item:hover{background:var(--soft)}
.badge{background:var(--primary);color:#fff;border-radius:999px;padding:1px 7px;font-size:.74rem}
.notif-wrapper{position:relative}
.notif-panel{position:absolute;right:0;top:calc(100% + 8px);width:330px;background:#fff;border:1px solid var(--border);border-radius:12px;box-shadow:0 14px 30px rgba(15,23,42,.15);z-index:200}
.notif-header{display:flex;align-items:center;justify-content:space-between;padding:12px 14px;border-bottom:1px solid var(--border);font-size:.86rem}
.notif-list{max-height:280px;overflow-y:auto}.notif-item{padding:10px 14px;border-bottom:1px solid var(--alt);font-size:.85rem}
.main-layout{max-width:1160px;margin:22px auto;padding:0 18px;display:grid;grid-template-columns:270px 1fr;gap:22px;align-items:start}
.card{background:var(--surface);border:1px solid var(--border);border-radius:var(--radius);padding:18px;box-shadow:var(--shadow);margin-bottom:16px}
.mini-profile{text-align:center}
.avatar-lg,.avatar-sm{border-radius:50%;background:linear-gradient(135deg,#4338ca,#0ea5e9);color:#fff;font-weight:700;display:inline-flex;align-items:center;justify-content:center;user-select:none;-webkit-tap-highlight-color:transparent}
.avatar-lg{width:62px;height:62px;font-size:1.45rem;margin-bottom:8px}
.avatar-sm{width:40px;height:40px;font-size:.95rem;flex-shrink:0}
.mini-stats{display:grid;grid-template-columns:1fr 1fr;border-top:1px solid var(--border);padding-top:10px;margin-top:10px}
.mini-stats strong{display:block;font-size:1.1rem;color:var(--primary)}.mini-stats span{font-size:.78rem;color:var(--muted)}
.side-nav{padding:8px;display:flex;flex-direction:column;gap:4px}
.side-link{display:flex;align-items:center;justify-content:space-between;border:none;background:transparent;padding:10px 12px;border-radius:8px;font:inherit;font-weight:600;color:#334155;cursor:pointer;text-align:left}
.side-link:hover{background:var(--alt)}.side-link.active{background:var(--soft);color:var(--primary)}
.dsa-tag,.dsa-pill{font-size:.72rem;font-weight:700;padding:2px 8px;border-radius:999px;background:var(--soft);color:var(--primary)}
.section-header{display:flex;align-items:center;justify-content:space-between;gap:12px;margin-bottom:14px}
.section-header h2{margin:0;font-size:1.22rem}.section-header p{margin:2px 0 0}
.toggle-check{display:flex;align-items:center;gap:6px;font-size:.86rem;cursor:pointer;white-space:nowrap}.toggle-check input{width:auto;margin:0}
.composer-footer{display:flex;align-items:center;justify-content:space-between;gap:10px}
.file-upload-label{display:inline-flex;align-items:center;gap:6px;padding:7px 12px;border-radius:8px;border:1px dashed var(--border);cursor:pointer;font-size:.84rem;font-weight:600}
.post-card-header{display:flex;align-items:center;justify-content:space-between;margin-bottom:10px}
.post-author-row{display:flex;align-items:center;gap:10px;cursor:pointer}
.post-title{margin:4px 0 6px;font-size:1.06rem}
.post-image{width:100%;max-height:360px;object-fit:cover;border-radius:10px;margin:10px 0;border:1px solid var(--border)}
.tags-row{display:flex;flex-wrap:wrap;gap:6px;margin:8px 0}
.tag-pill{background:var(--alt);border:1px solid var(--border);color:#334155;padding:2px 9px;border-radius:999px;font-size:.78rem;font-weight:600}
.post-actions{display:flex;align-items:center;gap:12px;border-top:1px solid var(--alt);padding-top:10px;margin-top:10px;flex-wrap:wrap}
.comments-box{margin-top:12px;padding-top:12px;border-top:1px solid var(--border)}
.comment-node{border-left:2px solid #cbd5e1;padding-left:12px;margin-top:10px}
.comment-form{display:flex;gap:8px;margin-top:8px}.comment-form input{margin-bottom:0}
.people-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(235px,1fr));gap:12px}
.person-card{border:1px solid var(--border);border-radius:10px;padding:14px;background:var(--alt);display:flex;flex-direction:column;justify-content:space-between;gap:10px}
.person-head{display:flex;align-items:center;gap:10px;cursor:pointer}.person-actions{display:flex;gap:8px;flex-wrap:wrap}
.bfs-bar{display:flex;align-items:center;gap:10px;margin-top:10px}.bfs-bar select{margin-bottom:0}
.bfs-result{margin-top:12px;padding:12px;background:var(--soft);border-radius:10px}
.chain-row{display:flex;flex-wrap:wrap;align-items:center;gap:8px;margin-top:8px}
.chain-node{background:#fff;border:1px solid #c7d2fe;padding:4px 10px;border-radius:999px;font-size:.83rem;font-weight:600;cursor:pointer}
.communities-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(290px,1fr));gap:14px}
.emoji-row{display:flex;gap:6px;flex-wrap:wrap;margin-top:6px}
.emoji-btn{background:var(--alt);border:1px solid var(--border);border-radius:999px;padding:3px 10px;font-size:.88rem;cursor:pointer;display:inline-flex;align-items:center;gap:4px;transition:background .15s}
.emoji-btn:hover{background:var(--soft);border-color:#c7d2fe}
.emoji-btn.reacted{background:#eef2ff;border-color:var(--primary);color:var(--primary)}
@media(max-width:860px){.main-layout{grid-template-columns:1fr}.navbar{flex-wrap:wrap}.search-wrapper{order:3;min-width:100%}}
</style>
</head>
<body>
<div id="toast" class="toast hidden"></div>

<div id="auth-screen" class="auth-screen">
  <div class="auth-card">
    <div class="auth-brand">
      <div class="logo-badge">CU</div>
      <div>
        <h1>ChanakyaConnect</h1>
        <p class="subtitle">Chanakya University Student Network &bull; Pure Python DSA</p>
      </div>
    </div>
    <div class="auth-tabs">
      <button id="tab-login-btn" class="auth-tab active" onclick="switchAuthTab('login')">Log In</button>
      <button id="tab-signup-btn" class="auth-tab" onclick="switchAuthTab('signup')">Sign Up</button>
    </div>
    <form id="login-form" class="auth-form" onsubmit="handleLogin(event)">
      <label>Username</label>
      <input id="login-username" type="text" placeholder="e.g. aarav" required />
      <label>Password</label>
      <input id="login-password" type="password" placeholder="Enter password" required />
      <button type="submit" class="btn btn-primary full-width">Log In</button>
    </form>
    <form id="signup-form" class="auth-form hidden" onsubmit="handleSignup(event)">
      <div class="grid-2">
        <div><label>Username</label><input id="su-username" type="text" placeholder="e.g. rahul_26" required /></div>
        <div><label>Password</label><input id="su-password" type="password" placeholder="Min 4 chars" required /></div>
      </div>
      <label>Full Name</label><input id="su-name" type="text" placeholder="e.g. Rahul Verma" required />
      <div class="grid-2">
        <div><label>Programme</label><input id="su-programme" type="text" value="B.Tech. CSE" required /></div>
        <div><label>Year</label><select id="su-year"><option>I Year</option><option selected>II Year</option><option>III Year</option><option>IV Year</option></select></div>
      </div>
      <label>Skills (comma-separated)</label><input id="su-skills" type="text" placeholder="Python, Graphs, Trees" />
      <label>Short Bio</label><textarea id="su-bio" rows="2" placeholder="Your projects & technical interests..."></textarea>
      <button type="submit" class="btn btn-primary full-width">Create Account</button>
    </form>
  </div>
</div>

<div id="app-shell" class="hidden">
  <header class="navbar">
    <div class="nav-left">
      <button class="btn btn-ghost btn-sm" onclick="handleBackNav()" title="Pop Navigation Stack">&larr; Back</button>
      <div class="nav-brand" onclick="navigateTo('feed')"><span class="logo-badge sm">CU</span><span>ChanakyaConnect</span></div>
    </div>
    <div class="search-wrapper">
      <input id="search-input" type="text" placeholder="Search students by name or username (Trie prefix)..." autocomplete="off" oninput="handleSearchInput(this.value)" onfocus="handleSearchInput(this.value)" />
      <div id="search-dropdown" class="search-dropdown hidden"></div>
    </div>
    <div class="nav-right">
      <button id="undo-btn" class="btn btn-outline btn-sm hidden" onclick="handleUndo()">&#8634; Undo</button>
      <div class="notif-wrapper">
        <button class="btn btn-ghost btn-sm" onclick="toggleNotifPanel()">&#128276; <span id="notif-badge" class="badge">0</span></button>
        <div id="notif-panel" class="notif-panel hidden">
          <div class="notif-header"><strong>Notifications</strong><div><button class="link-btn" onclick="clearAllNotifs()">Clear</button></div></div>
          <div id="notif-list" class="notif-list"></div>
        </div>
      </div>
      <button class="btn btn-ghost btn-sm" onclick="openProfile(state.currentUser.username)"><span id="nav-user-label">@user</span></button>
      <button class="btn btn-danger-outline btn-sm" onclick="handleLogout()">Log Out</button>
    </div>
  </header>

  <div class="main-layout">
    <aside>
      <div class="card mini-profile">
        <div class="avatar-lg" id="side-avatar">A</div>
        <h3 id="side-name" style="margin:0;">Student</h3>
        <p class="muted" id="side-meta"></p>
        <p class="muted" id="side-bio"></p>
        <div class="mini-stats">
          <div><strong id="side-conns">0</strong><span>Connections</span></div>
          <div><strong id="side-reqs">0</strong><span>Requests</span></div>
        </div>
      </div>
      <nav class="side-nav card">
        <button class="side-link active" data-view="feed" onclick="navigateTo('feed')">&#127968; Home Feed <span class="dsa-tag">MaxHeap</span></button>
        <button class="side-link" data-view="trending" onclick="navigateTo('trending')">&#128293; Trending <span class="dsa-tag">MaxHeap</span></button>
        <button class="side-link" data-view="network" onclick="navigateTo('network')">&#128101; My Network <span class="dsa-tag">Graph + BFS</span></button>
        <button class="side-link" data-view="communities" onclick="navigateTo('communities')">&#127760; Communities <span class="dsa-tag">Union-Find</span></button>
        <button class="side-link" data-view="profile" onclick="openProfile(state.currentUser.username)">&#128100; My Profile <span class="dsa-tag">HashTable</span></button>
        <button class="side-link" data-view="messages" onclick="navigateTo('messages')">&#128172; Messages <span id="msg-badge" class="badge hidden">0</span></button>
      </nav>
    </aside>

    <main>
      <section id="view-feed" class="view-section">
        <div class="card">
          <h3 style="margin-top:0;">Share a Project or Technical Idea</h3>
          <form onsubmit="handleCreatePost(event)">
            <input id="post-title" type="text" placeholder="Project / Idea Title" />
            <textarea id="post-content" rows="3" placeholder="What are you building at Chanakya University?"></textarea>
            <input id="post-tags" type="text" placeholder="Tags: Graphs, Python, AI" />
            <div id="post-image-previews" class="preview-row"></div>
            <div class="composer-footer">
              <label class="file-upload-label">&#128247; Attach Images<input id="post-image-file" type="file" accept="image/*" multiple onchange="handleImageFileSelect(event)" hidden /></label>
              <span id="post-image-name" class="muted"></span>
              <button type="submit" class="btn btn-primary">Publish Post</button>
            </div>
          </form>
        </div>
        <div class="section-header">
          <div><h2>Home Feed <span class="dsa-pill">K-way MaxHeap Merge</span></h2><p class="muted">Newest-first merge of connections' time-ordered posts.</p></div>
          <label class="toggle-check"><input type="checkbox" id="include-own-toggle" onchange="loadFeed()" /> Include my own posts</label>
        </div>
        <div id="feed-list"></div>
      </section>

      <section id="view-trending" class="view-section hidden">
        <div class="section-header"><div><h2>Trending Posts <span class="dsa-pill">MaxHeap</span></h2><p class="muted">Ranked by likes + 2&times;comments.</p></div></div>
        <div id="trending-list"></div>
      </section>

      <section id="view-network" class="view-section hidden">
        <div class="card"><h3>Pending Incoming Requests <span class="dsa-pill">FIFO Queue</span></h3><div id="incoming-list" class="people-grid"></div></div>
        <div class="card"><h3>People You May Know <span class="dsa-pill">Jaccard + MaxHeap</span></h3><div id="pymk-list" class="people-grid"></div></div>
        <div class="card"><h3>Your Connections <span class="dsa-pill">Adjacency List</span></h3><div id="connections-list" class="people-grid"></div></div>
        <div class="card"><h3>Sent Requests <span class="dsa-pill">Directed Pending</span></h3><div id="outgoing-list" class="people-grid"></div></div>
      </section>

      <section id="view-communities" class="view-section hidden">
        <div class="section-header"><div><h2>Student Communities <span class="dsa-pill">Union-Find</span></h2><p class="muted">Connected clusters computed in-memory from graph edges.</p></div></div>
        <div id="communities-list" class="communities-grid"></div>
      </section>

      <section id="view-profile" class="view-section hidden"><div id="profile-container"></div></section>

      <section id="view-messages" class="view-section hidden">
        <div class="section-header"><div><h2>Messages</h2><p class="muted">Chat with people you are connected with.</p></div></div>
        <div class="chat-layout">
          <div class="card chat-list" id="chat-list"></div>
          <div class="card chat-pane">
            <div id="chat-header" class="chat-header muted">Select a connection to start chatting.</div>
            <div id="chat-messages" class="chat-messages"></div>
            <form id="chat-form" class="chat-form hidden" onsubmit="sendChatMessage(event)">
              <input id="chat-input" type="text" maxlength="1000" placeholder="Type a message..." autocomplete="off" required />
              <button type="submit" class="btn btn-primary btn-sm">Send</button>
            </form>
          </div>
        </div>
      </section>

    </main>
  </div>
</div>

<script>
const state={token:localStorage.getItem("cc_token")||"",currentUser:null,currentView:"feed",pendingImages:[],chatWith:null,chatSig:"",searchTimer:null,viewingProfileUser:null};
function esc(s){return s==null?"":String(s).replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;").replace(/"/g,"&quot;").replace(/'/g,"&#39;");}
function ago(ts){const d=Math.max(0,Math.floor(Date.now()/1000-ts));if(d<60)return"Just now";if(d<3600)return Math.floor(d/60)+"m ago";if(d<86400)return Math.floor(d/3600)+"h ago";return new Date(ts*1000).toLocaleDateString();}
function toast(m,err=false){const el=document.getElementById("toast");el.textContent=m;el.className=err?"toast error":"toast";el.classList.remove("hidden");clearTimeout(el._t);el._t=setTimeout(()=>el.classList.add("hidden"),3000);}
async function api(u,o={}){const h={"Content-Type":"application/json",...(o.headers||{})};if(state.token)h["Authorization"]="Bearer "+state.token;const r=await fetch(u,{...o,headers:h});const d=await r.json();if(!r.ok||d.ok===false)throw new Error(d.error||d.message||"Failed");return d;}
function switchAuthTab(t){const l=t==="login";document.getElementById("tab-login-btn").classList.toggle("active",l);document.getElementById("tab-signup-btn").classList.toggle("active",!l);document.getElementById("login-form").classList.toggle("hidden",!l);document.getElementById("signup-form").classList.toggle("hidden",l);}
function fillDemo(u){document.getElementById("login-username").value=u;document.getElementById("login-password").value="pass123";}
async function handleLogin(e){e.preventDefault();try{const d=await api("/api/login",{method:"POST",body:JSON.stringify({username:document.getElementById("login-username").value,password:document.getElementById("login-password").value})});state.token=d.token;localStorage.setItem("cc_token",d.token);state.currentUser=d.user;await enterApp();toast("Welcome, "+d.user.name);}catch(err){toast(err.message,true);}}
async function handleSignup(e){e.preventDefault();try{const d=await api("/api/signup",{method:"POST",body:JSON.stringify({username:document.getElementById("su-username").value,password:document.getElementById("su-password").value,name:document.getElementById("su-name").value,programme:document.getElementById("su-programme").value,year:document.getElementById("su-year").value,skills:document.getElementById("su-skills").value,bio:document.getElementById("su-bio").value})});state.token=d.token;localStorage.setItem("cc_token",d.token);state.currentUser=d.user;await enterApp();toast("Account created!");}catch(err){toast(err.message,true);}}
async function handleLogout(){try{await api("/api/logout",{method:"POST",body:"{}"});}catch(_){}state.token="";state.currentUser=null;state.chatWith=null;state.chatSig="";localStorage.removeItem("cc_token");document.getElementById("app-shell").classList.add("hidden");document.getElementById("auth-screen").classList.remove("hidden");}
async function bootstrap(){if(!state.token)return;try{const m=await api("/api/me");state.currentUser=m.user;await enterApp();}catch(_){localStorage.removeItem("cc_token");state.token="";}}
async function enterApp(){document.getElementById("auth-screen").classList.add("hidden");document.getElementById("app-shell").classList.remove("hidden");await refreshTop();await navigateTo("feed");}
async function refreshTop(){const m=await api("/api/me");state.currentUser=m.user;const u=m.user;document.getElementById("nav-user-label").textContent="@"+u.username;document.getElementById("side-avatar").textContent=(u.name||u.username)[0].toUpperCase();document.getElementById("side-name").textContent=u.name;document.getElementById("side-meta").textContent=u.programme+" • "+u.year;document.getElementById("side-bio").textContent=u.bio||"No bio yet.";document.getElementById("side-conns").textContent=u.connections_count;document.getElementById("notif-badge").textContent=m.notifications_count;setMsgBadge(m.unread_messages||0);const net=await api("/api/network");document.getElementById("side-reqs").textContent=net.incoming_requests.length;const ub=document.getElementById("undo-btn");if(m.undo){ub.classList.remove("hidden");ub.title=m.undo.label;ub.textContent="↺ Undo ("+m.undo.count+")";}else ub.classList.add("hidden");}
async function navigateTo(v,target=null,push=true){state.currentView=v;if(push)await api("/api/nav/push",{method:"POST",body:JSON.stringify({view:v,target})});document.querySelectorAll(".view-section").forEach(s=>s.classList.add("hidden"));document.getElementById("view-"+v).classList.remove("hidden");document.querySelectorAll(".side-link").forEach(b=>b.classList.toggle("active",b.dataset.view===v));if(v==="feed")await loadFeed();else if(v==="trending")await loadTrending();else if(v==="network")await loadNetwork();else if(v==="communities")await loadCommunities();else if(v==="messages")await loadMessages();else if(v==="profile")await loadProfile(target||state.currentUser.username);}
async function handleBackNav(){const r=await api("/api/nav/pop",{method:"POST",body:"{}"});if(r.prev)await navigateTo(r.prev.view,r.prev.target,false);else toast("Navigation Stack is at root.");}
async function handleUndo(){try{const r=await api("/api/undo",{method:"POST",body:"{}"});toast(r.message);await refreshTop();await navigateTo(state.currentView,state.viewingProfileUser,false);}catch(err){toast(err.message,true);}}
function readFileAsDataUrl(f){return new Promise((res,rej)=>{const rd=new FileReader();rd.onload=()=>res(rd.result);rd.onerror=()=>rej(new Error("Could not read "+f.name));rd.readAsDataURL(f);});}
async function shrinkImage(f){const url=await readFileAsDataUrl(f);const fits=u=>u.length-u.indexOf(",")-1<=349524;if(fits(url)&&/^data:image\/(png|jpeg|jpg|gif|webp);base64,/.test(url))return url;if(f.type==="image/gif")throw new Error("GIF must be 256 KB or less.");return new Promise((res,rej)=>{const img=new Image();img.onload=()=>{const c=document.createElement("canvas");for(const max of [1200,900,640,480,320]){const r=Math.min(1,max/Math.max(img.width,img.height));c.width=Math.max(1,Math.round(img.width*r));c.height=Math.max(1,Math.round(img.height*r));const x=c.getContext("2d");x.fillStyle="#fff";x.fillRect(0,0,c.width,c.height);x.drawImage(img,0,0,c.width,c.height);for(const q of [.8,.6,.4]){const out=c.toDataURL("image/jpeg",q);if(fits(out))return res(out);}}rej(new Error("Image could not be compressed below 256 KB."));};img.onerror=()=>rej(new Error("Invalid image."));img.src=url;});}
async function handleImageFileSelect(e){const files=Array.from(e.target.files||[]);e.target.value="";if(!files.length)return;const room=10-state.pendingImages.length;if(files.length>room)toast("You can attach up to 10 images per post.",true);for(const f of files.slice(0,Math.max(room,0))){if(!f.type.startsWith("image/")){toast(f.name+" is not an image.",true);continue;}try{state.pendingImages.push({name:f.name,data:await shrinkImage(f)});}catch(err){toast(err.message,true);}}renderImagePreviews();}
function removePendingImage(i){state.pendingImages.splice(i,1);renderImagePreviews();}
function renderImagePreviews(){const n=state.pendingImages.length;document.getElementById("post-image-name").textContent=n?n+" image"+(n>1?"s":"")+" attached":"";document.getElementById("post-image-previews").innerHTML=state.pendingImages.map((im,i)=>`<div class="preview-item"><img src="${im.data}" alt="" /><button type="button" onclick="removePendingImage(${i})" title="Remove">&times;</button></div>`).join("");}
function renderGallery(p){const imgs=(p.image_urls&&p.image_urls.length)?p.image_urls:(p.image_url?[p.image_url]:[]);if(!imgs.length)return"";const cls=imgs.length<=4?"n"+imgs.length:"many";return`<div class="gallery ${cls}">${imgs.map(u=>`<img src="${esc(u)}" alt="Post image" onclick="window.open(this.src,'_blank')" />`).join("")}</div>`;}
async function handleCreatePost(e){e.preventDefault();try{await api("/api/posts",{method:"POST",body:JSON.stringify({title:document.getElementById("post-title").value,content:document.getElementById("post-content").value,tags:document.getElementById("post-tags").value,images:state.pendingImages.map(i=>i.data)})});["post-title","post-content","post-tags","post-image-file"].forEach(id=>document.getElementById(id).value="");state.pendingImages=[];renderImagePreviews();toast("Post published!");document.getElementById("include-own-toggle").checked=true;await loadFeed();}catch(err){toast(err.message,true);}}
async function loadFeed(){const inc=document.getElementById("include-own-toggle").checked?"1":"0";const d=await api("/api/feed?include_own="+inc);renderPosts("feed-list",d.posts,"No posts yet. Connect with peers or publish a post!");}
async function loadTrending(){const d=await api("/api/trending");renderPosts("trending-list",d.posts,"No liked/commented posts yet.");}
function renderCommentTree(c,pid){const rep=(c.replies||[]).map(r=>renderCommentTree(r,pid)).join("");const bid="rb-"+c.comment_id;return`<div class="comment-node"><div><button class="link-btn" onclick="openProfile('${esc(c.author)}')">@${esc(c.author)}</button> <span class="muted">&bull; ${ago(c.timestamp)}</span></div><div>${esc(c.text)}</div><button class="link-btn" onclick="document.getElementById('${bid}').classList.toggle('hidden')">Reply</button><form id="${bid}" class="comment-form hidden" onsubmit="submitComment(event,'${pid}','${c.comment_id}')"><input type="text" placeholder="Write a reply..." required /><button type="submit" class="btn btn-primary btn-sm">Reply</button></form>${rep}</div>`;}
function renderPosts(cid,posts,empty){const el=document.getElementById(cid);if(!posts.length){el.innerHTML=`<div class="card muted">${esc(empty)}</div>`;return;}el.innerHTML=posts.map(p=>{const mine=p.author===state.currentUser.username;const tags=(p.tags||[]).map(t=>`<span class="tag-pill">#${esc(t)}</span>`).join("");const comms=(p.comments||[]).map(c=>renderCommentTree(c,p.post_id)).join("");const emojis=["👍","🔥","🎉","💡","🤝"];const emojiRow=emojis.map(em=>{const reactions=p.reactions||{};const count=reactions[em]||0;const myReacts=p.my_reactions||[];const reacted=myReacts.includes(em);return`<button class="emoji-btn${reacted?" reacted":""}" onclick="toggleEmoji('${p.post_id}','${em}')">${em}${count>0?` <span>${count}</span>`:""}</button>`;}).join("");return`<article class="card"><div class="post-card-header"><div class="post-author-row" onclick="openProfile('${esc(p.author)}')"><div class="avatar-sm" style="-webkit-tap-highlight-color:transparent;outline:none;">${esc((p.author_name||p.author)[0].toUpperCase())}</div><div><strong>${esc(p.author_name)}</strong> <span class="muted">@${esc(p.author)}</span><div class="muted">${esc(p.author_programme)} &bull; ${esc(p.author_year)} &bull; ${ago(p.timestamp)}</div></div></div><div>${p.trend_score!==undefined?`<span class="dsa-pill">Score: ${p.trend_score}</span>`:""}${mine?`<button class="btn btn-danger-outline btn-sm" onclick="delPost('${p.post_id}')">Delete</button>`:""}</div></div>${p.title?`<h4 class="post-title">${esc(p.title)}</h4>`:""}<p>${esc(p.content)}</p>${renderGallery(p)}${tags?`<div class="tags-row">${tags}</div>`:""}<div class="post-actions"><button class="btn btn-outline btn-sm" onclick="likePost('${p.post_id}')">${p.liked_by_me?"❤️ Liked":"♡ Like"} (${p.likes_count})</button><button class="btn btn-ghost btn-sm" onclick="document.getElementById('cm-${p.post_id}').classList.toggle('hidden')">💬 Comments (${p.comments_count})</button></div><div class="emoji-row">${emojiRow}</div><div id="cm-${p.post_id}" class="comments-box ${p.comments_count?"":"hidden"}"><form class="comment-form" onsubmit="submitComment(event,'${p.post_id}',null)"><input type="text" placeholder="Add a comment..." required /><button type="submit" class="btn btn-primary btn-sm">Post</button></form>${comms}</div></article>`;}).join("");}
async function reloadPostContainer(){if(state.currentView==="feed")await loadFeed();else if(state.currentView==="trending")await loadTrending();else if(state.currentView==="profile")await loadProfile(state.viewingProfileUser||state.currentUser.username);}
async function likePost(pid){await api("/api/posts/like",{method:"POST",body:JSON.stringify({post_id:pid})});await reloadPostContainer();}
async function toggleEmoji(pid,emoji){await api("/api/posts/react",{method:"POST",body:JSON.stringify({post_id:pid,emoji:emoji})});await reloadPostContainer();}
async function submitComment(e,pid,parent){e.preventDefault();const inp=e.target.querySelector("input");await api("/api/posts/comment",{method:"POST",body:JSON.stringify({post_id:pid,text:inp.value,parent_comment_id:parent})});inp.value="";await reloadPostContainer();}
async function delPost(pid){const r=await api("/api/posts/delete",{method:"POST",body:JSON.stringify({post_id:pid})});toast(r.message);await refreshTop();await reloadPostContainer();}
async function loadNetwork(){const net=await api("/api/network");
document.getElementById("incoming-list").innerHTML=net.incoming_requests.length?net.incoming_requests.map(r=>`<div class="person-card"><div class="person-head" onclick="openProfile('${esc(r.user.username)}')"><div class="avatar-sm">${esc(r.user.name[0].toUpperCase())}</div><div><strong>${esc(r.user.name)}</strong><div class="muted">@${esc(r.user.username)} &bull; ${r.mutual_count} mutual</div></div></div><div class="person-actions"><button class="btn btn-primary btn-sm" onclick="netAct('/api/connections/accept',{sender:'${esc(r.user.username)}'})">Accept</button><button class="btn btn-danger-outline btn-sm" onclick="netAct('/api/connections/reject',{sender:'${esc(r.user.username)}'})">Reject</button></div></div>`).join(""):`<div class="muted">No incoming requests.</div>`;
document.getElementById("pymk-list").innerHTML=net.people_you_may_know.length?net.people_you_may_know.map(s=>`<div class="person-card"><div class="person-head" onclick="openProfile('${esc(s.user.username)}')"><div class="avatar-sm">${esc(s.user.name[0].toUpperCase())}</div><div><strong>${esc(s.user.name)}</strong><div class="muted">${esc(s.user.programme)}</div><div class="muted">Jaccard: <strong>${s.jaccard_score}</strong> &bull; ${s.mutual_count} mutual</div></div></div><div class="person-actions"><button class="btn btn-primary btn-sm" onclick="netAct('/api/connections/request',{target:'${esc(s.user.username)}'})">Connect</button></div></div>`).join(""):`<div class="muted">No suggestions right now.</div>`;
document.getElementById("connections-list").innerHTML=net.connections.length?net.connections.map(u=>`<div class="person-card"><div class="person-head" onclick="openProfile('${esc(u.username)}')"><div class="avatar-sm">${esc(u.name[0].toUpperCase())}</div><div><strong>${esc(u.name)}</strong><div class="muted">@${esc(u.username)} &bull; ${u.mutual_count} mutual</div></div></div><div class="person-actions"><button class="btn btn-primary btn-sm" onclick="openMessagesWith('${esc(u.username)}')">Message</button><button class="btn btn-outline btn-sm" onclick="openProfile('${esc(u.username)}')">Profile</button><button class="btn btn-danger-outline btn-sm" onclick="netAct('/api/connections/remove',{target:'${esc(u.username)}'})">Remove</button></div></div>`).join(""):`<div class="muted">No connections yet.</div>`;
document.getElementById("outgoing-list").innerHTML=net.outgoing_requests.length?net.outgoing_requests.map(u=>`<div class="person-card"><div class="person-head" onclick="openProfile('${esc(u.username)}')"><div class="avatar-sm">${esc(u.name[0].toUpperCase())}</div><div><strong>${esc(u.name)}</strong><div class="muted">@${esc(u.username)} &bull; Pending</div></div></div><div class="person-actions"><button class="btn btn-outline btn-sm" onclick="netAct('/api/connections/cancel',{target:'${esc(u.username)}'})">Cancel</button></div></div>`).join(""):`<div class="muted">No sent requests.</div>`;}
async function netAct(ep,payload){try{const r=await api(ep,{method:"POST",body:JSON.stringify(payload)});toast(r.message);await refreshTop();if(state.currentView==="network")await loadNetwork();else if(state.currentView==="profile")await loadProfile(state.viewingProfileUser);}catch(err){toast(err.message,true);}}
async function loadCommunities(){const d=await api("/api/communities");document.getElementById("communities-list").innerHTML=d.communities.map(c=>`<div class="card"><h3>${esc(c.name)}</h3><p class="muted">${c.size} students &bull; ${c.connections_count} connections</p><div class="tags-row">${(c.top_skills||[]).map(s=>`<span class="tag-pill">${esc(s)}</span>`).join("")}</div><div class="chain-row">${c.members.map(m=>`<span class="chain-node" onclick="openProfile('${esc(m.username)}')">${esc(m.name)}</span>`).join("")}</div></div>`).join("");}
async function openProfile(u){state.viewingProfileUser=u;await navigateTo("profile",u,true);}
async function loadProfile(u){state.viewingProfileUser=u;const d=await api("/api/profile?username="+encodeURIComponent(u));const usr=d.user,self=d.connection_status==="self";let act="";if(d.connection_status==="connected")act=`<button class="btn btn-primary btn-sm" onclick="openMessagesWith('${esc(usr.username)}')">&#128172; Message</button><button class="btn btn-danger-outline btn-sm" onclick="netAct('/api/connections/remove',{target:'${esc(usr.username)}'})">Remove Connection</button>`;else if(d.connection_status==="outgoing_pending")act=`<button class="btn btn-outline btn-sm" onclick="netAct('/api/connections/cancel',{target:'${esc(usr.username)}'})">Cancel Request</button>`;else if(d.connection_status==="incoming_pending")act=`<button class="btn btn-primary btn-sm" onclick="netAct('/api/connections/accept',{sender:'${esc(usr.username)}'})">Accept</button><button class="btn btn-danger-outline btn-sm" onclick="netAct('/api/connections/reject',{sender:'${esc(usr.username)}'})">Reject</button>`;else if(!self)act=`<button class="btn btn-primary btn-sm" onclick="netAct('/api/connections/request',{target:'${esc(usr.username)}'})">Connect</button>`;
const bfsHtml=!self&&d.degree!==null?`<div class="bfs-result"><strong>BFS Degree:</strong> ${d.degree} <div class="chain-row">${d.shortest_chain.map(n=>`<span class="chain-node" onclick="openProfile('${esc(n.username)}')">${esc(n.name)}</span>`).join(" &rarr; ")}</div></div>`:!self?`<div class="bfs-result">Disconnected (no path).</div>`:"";
const mutHtml=!self&&d.mutual_connections.length?`<div style="margin-top:10px;"><strong>Mutual (${d.mutual_connections.length}):</strong><div class="chain-row">${d.mutual_connections.map(m=>`<span class="chain-node" onclick="openProfile('${esc(m.username)}')">${esc(m.name)}</span>`).join("")}</div></div>`:"";
const editHtml=self?`<div class="card"><h3>Edit Profile</h3><form onsubmit="saveProfile(event)"><div class="grid-2"><input id="ep-name" value="${esc(usr.name)}" required /><input id="ep-prog" value="${esc(usr.programme)}" required /></div><div class="grid-2"><input id="ep-year" value="${esc(usr.year)}" required /><input id="ep-skills" value="${esc(usr.skills.join(", "))}" /></div><textarea id="ep-bio" rows="2">${esc(usr.bio)}</textarea><button type="submit" class="btn btn-primary btn-sm">Save Profile</button></form></div>`:"";
document.getElementById("profile-container").innerHTML=`<div class="card"><div class="post-card-header"><div class="post-author-row"><div class="avatar-lg" style="margin:0;">${esc(usr.name[0].toUpperCase())}</div><div><h2 style="margin:0;">${esc(usr.name)}</h2><div class="muted">@${esc(usr.username)} &bull; ${esc(usr.programme)} &bull; ${esc(usr.year)} &bull; ${usr.connections_count} Connections</div></div></div><div class="person-actions">${act}</div></div><p>${esc(usr.bio||"")}</p><div class="tags-row">${usr.skills.map(s=>`<span class="tag-pill">${esc(s)}</span>`).join("")}</div>${bfsHtml}${mutHtml}</div>${editHtml}<h3>Posts (${d.posts.length})</h3><div id="profile-posts"></div>`;renderPosts("profile-posts",d.posts,"No posts yet.");}
async function saveProfile(e){e.preventDefault();await api("/api/profile/update",{method:"POST",body:JSON.stringify({name:document.getElementById("ep-name").value,programme:document.getElementById("ep-prog").value,year:document.getElementById("ep-year").value,skills:document.getElementById("ep-skills").value,bio:document.getElementById("ep-bio").value})});toast("Profile updated!");await refreshTop();await loadProfile(state.currentUser.username);}
function handleSearchInput(v){clearTimeout(state.searchTimer);const dd=document.getElementById("search-dropdown");if(!v.trim()){dd.classList.add("hidden");return;}state.searchTimer=setTimeout(async()=>{const d=await api("/api/search?q="+encodeURIComponent(v.trim()));dd.innerHTML=d.results.length?d.results.map(u=>`<div class="search-item" onclick="document.getElementById('search-dropdown').classList.add('hidden');document.getElementById('search-input').value='';openProfile('${esc(u.username)}')"><div><strong>${esc(u.name)}</strong> <span class="muted">@${esc(u.username)}</span></div><span class="dsa-pill">${u.is_self?"You":u.degree?u.degree+" deg":"Unconnected"}</span></div>`).join(""):`<div class="search-item muted">No match</div>`;dd.classList.remove("hidden");},120);}
async function toggleNotifPanel(){const p=document.getElementById("notif-panel");p.classList.toggle("hidden");if(!p.classList.contains("hidden"))await loadNotifs();}
async function loadNotifs(){const d=await api("/api/notifications");document.getElementById("notif-badge").textContent=d.notifications.length;document.getElementById("notif-list").innerHTML=d.notifications.length?d.notifications.map(n=>`<div class="notif-item"><strong>${esc(n.actor_name)}</strong> ${esc(n.message)}<div class="muted">${ago(n.timestamp)}</div></div>`).join(""):`<div class="notif-item muted">No notifications yet.</div>`;}
async function clearAllNotifs(){await api("/api/notifications/clear",{method:"POST",body:"{}"});await loadNotifs();}
function fmtTime(ts){return new Date(ts*1000).toLocaleTimeString([],{hour:"2-digit",minute:"2-digit"});}
function setMsgBadge(n){const b=document.getElementById("msg-badge");if(!b)return;b.textContent=n;b.classList.toggle("hidden",!n);}
function openMessagesWith(u){state.chatWith=u;state.chatSig="";navigateTo("messages");}
async function loadMessages(){await loadInbox();if(state.chatWith)await openChat(state.chatWith,false);}
async function loadInbox(){const d=await api("/api/messages/inbox");setMsgBadge(d.unread_total);const el=document.getElementById("chat-list");el.innerHTML=d.conversations.length?d.conversations.map(c=>`<div class="chat-item${state.chatWith===c.username?" active":""}" onclick="openChat('${esc(c.username)}')"><div class="meta"><strong>${esc(c.name)}</strong><div class="muted">${c.last_text?(c.last_from_me?"You: ":"")+esc(c.last_text):"@"+esc(c.username)}</div></div>${c.unread?`<span class="badge">${c.unread}</span>`:""}</div>`).join(""):`<div class="muted" style="padding:10px;">Connect with someone to start chatting.</div>`;}
async function openChat(u,quiet=false){state.chatWith=u;const d=await api("/api/messages?with="+encodeURIComponent(u));const sig=u+"|"+d.messages.length+"|"+(d.messages.length?d.messages[d.messages.length-1].msg_id:"")+"|"+d.can_message;if(quiet&&state.chatSig===sig)return;state.chatSig=sig;const box=document.getElementById("chat-messages");const stick=!quiet||box.scrollHeight-box.scrollTop-box.clientHeight<60;document.getElementById("chat-header").innerHTML=`<span style="cursor:pointer" onclick="openProfile('${esc(d.user.username)}')">${esc(d.user.name)} <span class="muted">@${esc(d.user.username)}</span></span>`;box.innerHTML=(d.messages.length?d.messages.map(m=>`<div class="bubble ${m.from===state.currentUser.username?"me":"them"}">${esc(m.text)}<small>${fmtTime(m.timestamp)}</small></div>`).join(""):`<div class="muted">No messages yet. Say hello!</div>`)+(d.can_message?"":`<div class="muted" style="text-align:center">You are no longer connected, so new messages can't be sent.</div>`);document.getElementById("chat-form").classList.toggle("hidden",!d.can_message);if(stick)box.scrollTop=box.scrollHeight;if(!quiet){document.getElementById("chat-input").focus();await loadInbox();}}
async function sendChatMessage(e){e.preventDefault();const inp=document.getElementById("chat-input");const text=inp.value.trim();if(!text||!state.chatWith)return;try{await api("/api/messages/send",{method:"POST",body:JSON.stringify({to:state.chatWith,text})});inp.value="";state.chatSig="";await openChat(state.chatWith,false);}catch(err){toast(err.message,true);}}
let _pollTick=0;
async function pollMessages(){if(!state.token||!state.currentUser)return;try{if(state.currentView==="messages"){if(state.chatWith)await openChat(state.chatWith,true);await loadInbox();}else if(++_pollTick%4===0){const m=await api("/api/me");setMsgBadge(m.unread_messages||0);}}catch(_){}}
setInterval(pollMessages,4000);
bootstrap();
</script>
</body>
</html>
"""


# ==============================================================================
# 8. HTTP SERVER & REST API
# ==============================================================================
def _join_remote_and_exit():
    """python chanakya_connect1.py --join 192.168.1.5:5000
    Opens the HOST laptop's app in the browser. No local server and no local data
    folder are created, so everyone shares ONE user database (the host's)."""
    args = sys.argv[1:]
    if "--join" not in args:
        return
    i = args.index("--join")
    target = args[i + 1].strip() if i + 1 < len(args) else ""
    if not target:
        print("Usage: python chanakya_connect1.py --join <host-ip>[:port]   e.g. --join 192.168.1.5:5000")
        sys.exit(1)
    if not target.startswith(("http://", "https://")):
        target = "http://" + target
    host_part = target.split("://", 1)[1].split("/", 1)[0]
    if ":" not in host_part:
        target = target.rstrip("/") + ":5000"
    print(f"Opening ChanakyaConnect hosted at {target}")
    print("(This laptop is NOT running its own copy - you are using the host's shared data.)")
    webbrowser.open(target)
    sys.exit(0)


if __name__ == "__main__":
    _join_remote_and_exit()

ENGINE = ChanakyaNetEngine(data_dir=os.environ.get("DATA_DIR") or None)
ENGINE_LOCK = threading.RLock()


class ChanakyaHTTPServer(ThreadingHTTPServer):
    allow_reuse_address = True
    daemon_threads = True


class ChanakyaRequestHandler(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        print(f"[ChanakyaConnect] {self.address_string()} - {format % args}")

    def _send_json(self, status, payload):
        body = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _send_html(self, html_text):
        body = html_text.encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _send_upload(self, filepath):
        if not os.path.isfile(filepath):
            self.send_error(404, "Not found")
            return
        mime, _ = mimetypes.guess_type(filepath)
        with open(filepath, "rb") as f:
            data = f.read()
        self.send_response(200)
        self.send_header("Content-Type", mime or "application/octet-stream")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _read_json(self):
        length = int(self.headers.get("Content-Length", "0") or 0)
        if length == 0:
            return {}
        if length > 4 * 1024 * 1024:
            raise ValueError("Payload too large")
        return json.loads(self.rfile.read(length).decode("utf-8"))

    def _auth_user(self):
        auth = self.headers.get("Authorization", "")
        token = auth[7:].strip() if auth.startswith("Bearer ") else ""
        if not token:
            return None, ""
        with ENGINE_LOCK:
            return ENGINE.get_session_user(token), token

    def do_GET(self):
        with ENGINE_LOCK:
            if ENGINE.storage_failed:
                return self._send_json(503, {"ok": False, "error": "Storage unavailable; restart server."})
            try:
                return self._handle_get()
            except CloudStorageError:
                return self._send_json(503, {"ok": False, "error": "Storage unavailable; restart server."})

    def _handle_get(self):
        parsed = urllib.parse.urlparse(self.path)
        path, query = parsed.path, urllib.parse.parse_qs(parsed.query)

        if path == "/health":
            return self._send_json(200, {"ok": True})
        if path in ("/", "/index.html"):
            return self._send_html(HTML_PAGE)
        if path.startswith("/uploads/"):
            return self._send_upload(os.path.join(ENGINE.uploads_dir, os.path.basename(path)))

        username, _ = self._auth_user()
        if not username:
            return self._send_json(401, {"ok": False, "error": "Please log in first."})

        with ENGINE_LOCK:
            if path == "/api/me":
                _, _, prof = ENGINE.get_profile(username, username)
                return self._send_json(200, {
                    "ok": True,
                    "user": prof["user"],
                    "undo": ENGINE.get_undo_peek(username),
                    "notifications_count": len(ENGINE.get_notifications(username)),
                    "unread_messages": ENGINE.get_unread_total(username),
                })
            if path == "/api/feed":
                inc = query.get("include_own", ["0"])[0] == "1"
                return self._send_json(200, {"ok": True, "posts": ENGINE.get_home_feed(username, include_own=inc)})
            if path == "/api/trending":
                return self._send_json(200, {"ok": True, "posts": ENGINE.get_trending_posts(username)})
            if path == "/api/network":
                return self._send_json(200, {"ok": True, **ENGINE.get_network_overview(username)})
            if path == "/api/communities":
                return self._send_json(200, {"ok": True, "communities": ENGINE.get_communities()})
            if path == "/api/search":
                return self._send_json(200, {"ok": True, "results": ENGINE.search_users(query.get("q", [""])[0], username)})
            if path == "/api/profile":
                ok, msg, data = ENGINE.get_profile(username, query.get("username", [username])[0])
                return self._send_json(200 if ok else 404, {"ok": ok, **(data or {"error": msg})})
            if path == "/api/notifications":
                return self._send_json(200, {"ok": True, "notifications": ENGINE.get_notifications(username)})
            if path == "/api/messages/inbox":
                convs = ENGINE.get_inbox(username)
                return self._send_json(200, {"ok": True, "conversations": convs,
                                             "unread_total": sum(c["unread"] for c in convs)})
            if path == "/api/messages":
                ok, msg, data = ENGINE.get_conversation(username, query.get("with", [""])[0])
                return self._send_json(200 if ok else 404, {"ok": ok, **(data or {"error": msg})})
            if path == "/api/users":
                return self._send_json(200, {
                    "ok": True,
                    "users": [ENGINE._public_user(ENGINE.users.get(u)) for u in sorted(ENGINE.users.keys().to_list())],
                })
        return self._send_json(404, {"ok": False, "error": "Not found"})

    def do_POST(self):
        with ENGINE_LOCK:
            if ENGINE.storage_failed:
                return self._send_json(503, {"ok": False, "error": "Storage unavailable; restart server."})
            try:
                return self._handle_post()
            except CloudStorageError:
                return self._send_json(503, {"ok": False, "error": "Storage unavailable; restart server."})

    def _handle_post(self):
        path = urllib.parse.urlparse(self.path).path
        try:
            body = self._read_json()
        except Exception as exc:
            return self._send_json(400, {"ok": False, "error": str(exc)})

        if path == "/api/signup":
            with ENGINE_LOCK:
                ok, msg, data = ENGINE.signup(
                    body.get("username"), body.get("password"), body.get("name"),
                    body.get("programme"), body.get("year"), body.get("bio", ""), body.get("skills", ""),
                )
            return self._send_json(201 if ok else 400, {"ok": ok, "message": msg, **(data or {"error": msg})})

        if path == "/api/login":
            with ENGINE_LOCK:
                ok, msg, data = ENGINE.login(body.get("username"), body.get("password"))
            return self._send_json(200 if ok else 401, {"ok": ok, "message": msg, **(data or {"error": msg})})

        username, token = self._auth_user()
        if not username:
            return self._send_json(401, {"ok": False, "error": "Please log in first."})

        with ENGINE_LOCK:
            if path == "/api/logout":
                ENGINE.logout(token)
                return self._send_json(200, {"ok": True})
            if path == "/api/profile/update":
                ok, msg, udata = ENGINE.update_profile(
                    username, body.get("name"), body.get("programme"),
                    body.get("year"), body.get("bio"), body.get("skills"),
                )
                return self._send_json(200 if ok else 400, {"ok": ok, "message": msg, "user": udata})
            if path == "/api/posts":
                ok, msg, pdata = ENGINE.create_post(
                    username, body.get("content", ""), body.get("title", ""),
                    body.get("image_data", ""), body.get("tags", ""), body.get("images"),
                )
                return self._send_json(201 if ok else 400, {"ok": ok, "message": msg, "post": pdata})
            if path == "/api/posts/delete":
                ok, msg = ENGINE.delete_post(username, body.get("post_id", ""))
                return self._send_json(200 if ok else 400, {"ok": ok, "message": msg})
            if path == "/api/posts/like":
                ok, msg, data = ENGINE.toggle_like(username, body.get("post_id", ""))
                return self._send_json(200 if ok else 404, {"ok": ok, **(data or {"error": msg})})
            if path == "/api/posts/react":
                ok, msg, data = ENGINE.toggle_reaction(username, body.get("post_id", ""), body.get("emoji", ""))
                return self._send_json(200 if ok else 404, {"ok": ok, **(data or {"error": msg})})
            if path == "/api/posts/comment":
                ok, msg, pdata = ENGINE.add_comment(username, body.get("post_id", ""), body.get("text", ""), body.get("parent_comment_id"))
                return self._send_json(200 if ok else 400, {"ok": ok, "message": msg, "post": pdata})
            if path == "/api/connections/request":
                ok, msg = ENGINE.send_connection_request(username, body.get("target", ""))
                return self._send_json(200 if ok else 400, {"ok": ok, "message": msg})
            if path == "/api/connections/accept":
                ok, msg = ENGINE.accept_connection_request(username, body.get("sender", ""))
                return self._send_json(200 if ok else 400, {"ok": ok, "message": msg})
            if path == "/api/connections/reject":
                ok, msg = ENGINE.reject_connection_request(username, body.get("sender", ""))
                return self._send_json(200 if ok else 400, {"ok": ok, "message": msg})
            if path == "/api/connections/cancel":
                ok, msg = ENGINE.cancel_connection_request(username, body.get("target", ""))
                return self._send_json(200 if ok else 400, {"ok": ok, "message": msg})
            if path == "/api/connections/remove":
                ok, msg = ENGINE.remove_connection(username, body.get("target", ""))
                return self._send_json(200 if ok else 400, {"ok": ok, "message": msg})
            if path == "/api/undo":
                ok, msg = ENGINE.undo_last_action(username)
                return self._send_json(200 if ok else 400, {"ok": ok, "message": msg})
            if path == "/api/nav/push":
                hist = ENGINE.push_navigation(username, body.get("view", "feed"), body.get("target"))
                return self._send_json(200, {"ok": True, "history": hist})
            if path == "/api/nav/pop":
                prev, hist = ENGINE.pop_navigation(username)
                return self._send_json(200, {"ok": True, "prev": prev, "history": hist})
            if path == "/api/messages/send":
                ok, msg, data = ENGINE.send_message(username, body.get("to", ""), body.get("text", ""))
                return self._send_json(200 if ok else 400, {"ok": ok, "message": msg, "sent": data})
            if path == "/api/notifications/clear":
                ENGINE.clear_notifications(username)
                return self._send_json(200, {"ok": True})
        return self._send_json(404, {"ok": False, "error": "Endpoint not found"})


def _lan_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))
        return s.getsockname()[0]
    except OSError:
        return "127.0.0.1"
    finally:
        s.close()


def main():
    # HOST=127.0.0.1 keeps it private to this laptop; default 0.0.0.0 lets other
    # devices on the same Wi-Fi/LAN open the same app (and the same user database).
    host = os.environ.get("HOST", "0.0.0.0")
    port = int(os.environ.get("PORT", "5000"))
    server = ChanakyaHTTPServer((host, port), ChanakyaRequestHandler)
    url = f"http://127.0.0.1:{port}"
    print("=" * 60)
    print("  ChanakyaConnect (Pure Python DSA Web App)")
    print(f"  This laptop : {url}")
    if host in ("0.0.0.0", ""):
        lan = f"{_lan_ip()}:{port}"
        print(f"  FRIENDS on the same Wi-Fi: open  http://{lan}  in a browser")
        print(f"                       or run: python chanakya_connect1.py --join {lan}")
        print("  (Friends must NOT run their own copy - that creates a separate database.)")
    print(f"  Data folder : {ENGINE.data_dir}")
    print(f"  Users: {len(ENGINE.users.keys())} | Known user IDs: {len(ENGINE.known_ids)}")
    print("  Press Ctrl+C to stop.")
    print("=" * 60)
    if os.environ.get("OPEN_BROWSER") == "1":
        threading.Timer(0.6, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nServer stopped.")
        server.server_close()


if __name__ == "__main__":
    main()
