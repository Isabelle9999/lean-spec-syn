

### Current numbers (run_89, 8 benchmarks, full pipeline with refinement)
- Total generated: 155 specs across 8 benchmarks
- Rejected at gates: 41 (27% rejection rate)
- Kernel-proved: 114 (74% of generated, 100% of survived)
- Validated (unproved): 0
- Average soundness: 0.74
- Average precision: 1.00 (all 8 benchmarks)
- Average uniqueness: 0.92
- Best benchmark: gcd 1.00 soundness (19/19 proved)
- Worst benchmark: binarySearch 0.48 (10/21 proved)
- Zero timeouts across all 8 benchmarks

### VERINA (run_90, 172/189 benchmarks completed - my pc crashed, full pipeline with refinement)
- Total generated: 2,759 specs
- Rejected: 1,754 (64%)
  - Typecheck: 651
  - Eval: 0
  - Vacuity: 1,103
- Kernel-proved: 1,003 (36% of generated, 100% of survived)
- Validated (unproved): 0
- Average soundness: 0.358
- Average precision: 1.00 (139 benchmarks measured)
- Average uniqueness: 0.966
- Benchmarks with ≥1 proved: 147/172 (85%)
- Benchmarks with soundness >0.5: 42/172 (24%)
- Best benchmark: 0.94 soundness
- Worst: 25 benchmarks with 0 proved



### Spec Generation:

- LLM generates safe/easy specs, misses important properties like sorted, permutation (improvement) — need iterative generation like AutoSpec's 5-round loop
- 27% rejection rate from typecheck failures (improvement) — need more rounds of generate-verify-fix, currently only 1 retry
- Could add program slicing — whole function goes to LLM, hard for complex multi-function code (improvement) — SLD-Spec decomposes first
- No ground-truth-guided generation for VERINA postcond (improvement) — could tell LLM to prove the known postcond
- Duplicate specs pass through dedup with different variable names (functional) — normalization regex doesn't catch m n vs a b
- Concrete-value specs still generated despite prompt saying don't (functional) — prompt constraint not strong enough or LLM ignores it

- go through every LLM prompt and experiment with what produce the best results
Extract every prompt from synth.py (the command above shows them all)
For each prompt, collect 100+ outputs across different functions
Measure what % typecheck, proved, duplicates
Identify patterns in failures 
Add one constraint at a time, re-measure, keep what helps

For Verina
- LLM generates precondition-restatements instead of postconditions (1,103 vacuity kills). The prompt includes postcond body which contains both precondition properties AND postcondition properties. The LLM copies the precondition part (nums.length > 0) as a standalone spec. It's true but says nothing about the function's output. Fix: explicitly tell the LLM "generate specs about the RETURN VALUE, not about the input. Every spec must reference the function call in the conclusion."
- LLM generates specs with wrong syntax (651 typecheck failures). Missing quantifiers, wrong variable scoping, referencing undefined identifiers. The gate 1 retry fixes some but only 1 round. Fix: iterative generation (3 rounds of generate → typecheck → feed error → regenerate).

### Proof Search:

- Bare Lean fails all the time ( NN predictor would be good here), Mathlib does most work
- No tree search — flat batch only (improvement) — VERITAS shows tree search finds multi-step proofs batch can't
- could add auxiliary lemma generation before main proof (improvement) — Goedel generates helper lemmas first
- LLM fallbacks not used because Mathlib catches everything on dev benchmarks (not a bug), which will matter on more benchmarks where Mathlib won't match

### Refinement:

- Mutation loop finds no weaknesses across ALL 8 benchmarks (functional)......... — either batch check isn't detecting weaknesses, or mutations aren't diverse enough. Need verify by manually create a KNOWN weak spec, run mutation, see if it catches it
- Adversarial tier finds no successes across ALL 8 benchmarks (functional) — need to verify if the LLM actually producing functions that satisfy the specs
- the mutation part currently is over simplified, follow LLMorpheus + other mutaiton papers more closely  
- Functional correctness metric shows 0.00 (functional) — postcond matching broken
- Precision 1.00 everywhere based on thin evidence (0 certified mutants for most benchmarks) (functional) — precision is technically correct but meaningless without diverse mutants







 "the proof search adn refinement iimprovements are easier to manage, there are plenty of systematic wayys to do it, pretty done the tasks in issue.md. right now I'm spendign al lmy time in spec generaiton, I feel there's only so much I can do to improve the spec qulality, and tht is, modifying th prompts or creating something similar to claude.md, however still more trivial adn less in control. 
 
 Should I be adding RL int hre so that more data we feed into, better quality it produces? after every succesfful specs geenrated, the machines learns the pattern to produce better spec
 
 Are ther any other better wasys you guys can think of 
 
 I'm also thinking to SFT before the RL, helps go faster, supervised finetunign model first 

 RL starts from a base model that knows nothing about Lean specs. It generates thousands of garbage specs, gets negative rewards, slowly learns. Takes days of GPU time. 


In general, I still feels like I'm stackign u existing techniques, there may be a smarter way or creatign something new from it but I don't know. 
 "

 1. RL with verifier feedback (SpecRL approach, adapted to Lean). Reward = did the spec typecheck (R1) + did it get proved (R2) + did it survive mutation (R3). Train a small model (Qwen 7B) on your existing runs — you have 90 runs with thousands of pass/fail examples. The model LEARNS what typechecks and what doesn't. But: needs GPU, needs training pipeline, 2-4 weeks of engineering. Separate project.

 Supervised fine-tuning (SFT): Show the model 1,003 examples of (function → good spec). The model learns to copy the pattern. Like a student studying solved examples before an exam. No trial and error. Just "here's what a good answer looks like, learn to produce similar ones." Cheaper, faster, but the model only learns from YOUR examples — if your examples have blind spots, the model inherits them.

2. Retrieval-augmented generation. Instead of generating from scratch, SEARCH Mathlib for existing theorems about similar functions, then adapt them. If Mathlib has theorem List.length_map : (l.map f).length = l.length, and your function is like map, the LLM sees this theorem and generates an analogous one. RocqStar (2025) does this for Rocq. ReProver does this for Lean proofs. Nobody does it for spec generation in Lean. This is achievable in 1 week — use Mathlib search, embed results in prompt.

3. Self-play / curriculum learning (ANCORA approach). 
Th e simplest way is 
SAVE the good geenrated specs every time, LLM use that growing storage 
Could be more efficient, but i'm worried that it limits or supresses the LLM to genrate new kinds of theorem  


