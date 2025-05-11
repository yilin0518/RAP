use rustc_middle::mir::{BasicBlock, BasicBlocks};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum VisitState {
    NotVisited,
    Visiting,
    Visited,
}

pub fn has_cycle<'tcx>(blocks: &BasicBlocks<'tcx>) -> bool {
    let num_blocks = blocks.len();
    let mut state = vec![VisitState::NotVisited; num_blocks];
    fn dfs<'tcx>(blocks: &BasicBlocks<'tcx>, bb: BasicBlock, state: &mut [VisitState]) -> bool {
        let idx = bb.index();
        match state[idx] {
            VisitState::Visiting => return true,
            VisitState::Visited => return false, 
            VisitState::NotVisited => {
                state[idx] = VisitState::Visiting;
                let successors = blocks[bb].terminator().successors();
                for succ in successors {
                    if dfs(blocks, succ, state) {
                        return true;
                    }
                }
                state[idx] = VisitState::Visited;
                false
            }
        }
    }
    for (bb, _) in blocks.iter_enumerated() {
        if state[bb.index()] == VisitState::NotVisited {
            if dfs(blocks, bb, &mut state) {
                return true;
            }
        }
    }
    false
}
