fn main() {
    mod sequences {
        use std::collections::{LinkedList, VecDeque};
        fn t() {
            let _v: Vec<i32> = Vec::new();
            let _s: String = String::from("test");
            let _vd: VecDeque<i32> = VecDeque::new();
            let _link: LinkedList<i32> = LinkedList::new();
        }
    }

    mod maps {
        use std::collections::{BTreeMap, HashMap};
        fn t() {
            let _hash: HashMap<i32, i32> = HashMap::new();
            let _btree: BTreeMap<i32, i32> = BTreeMap::new();
        }
    }

    mod sets {
        use std::collections::{BTreeSet, HashSet};
        fn t() {
            let _hash: HashSet<i32> = HashSet::new();
            let _btree: BTreeSet<i32> = BTreeSet::new();
        }
    }

    mod misc {
        use std::collections::BinaryHeap;
        fn t() {
            let _heap: BinaryHeap<i32> = BinaryHeap::new();
        }
    }
}