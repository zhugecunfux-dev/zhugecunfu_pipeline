# Zhugecunfu Pipeline

A pipeline for auto-formalizing natural language mathematical problems into Lean 4 code and automatically proving them.

## Overview

This pipeline consists of two main stages:
1. **Formalization** (`main_v1.py`): Converts natural language math problems into Lean 4 formal statements
2. **Proving** (`prover_test.py`): Attempts to prove the formalized Lean 4 statements

## Prerequisites

- Python 3.8+
- Lean 4 server running locally
- Local LLM servers (for formalization, semantic checking, and proving)

## Installation

1. Clone the repository:
```bash
git clone <repository-url>
cd zhugecunfu_pipeline
```

2. Install dependencies:
```bash
pip install -r requirements.txt
```

3. Install the kimina_client package (if not available via pip):
```bash
# Follow the installation instructions for kimina_client
```

## Configuration

Before running the pipeline, you need to configure the following settings:

### 1. Update Model URLs and Names

In **`zhugecunfu/main_v1.py`**, update the following configurations:

```python
# Line 34: Formalizer model configuration
formalizer = ModelCalling(
    "your_local_model_name",  # Change this to your model name
    url="your_local_url",     # Change this to your local LLM server URL
    system_prompt=system_prompt
)

# Line 36: Lean server URL
LEAN_SERVER_URL = "your_local_lean_server_url"  # Change this to your Lean server URL

# Line 45: Semantic checker model configuration
semantic_checker = ModelCalling(
    "your_local_model_name",  # Change this to your model name
    url="your_local_url",     # Change this to your local LLM server URL
    system_prompt=system_prompt,
    params=params
)
```

In **`zhugecunfu/prover_test.py`**, update:

```python
# Line 30: Lean server URL
LEAN_SERVER_URL = "your_local_lean_server_url"  # Change this to your Lean server URL

# Line 35: Prover model configuration
prover = ModelCalling(
    "your_local_model_name",  # Change this to your model name
    url="your_local_url",     # Change this to your local LLM server URL
    system_prompt=system_prompt
)
```

### 2. Update Prompt Paths

In **`zhugecunfu/main_v1.py`**, update the prompt file paths:

```python
# Line 31: Formalizer system prompt path
file_path = r"your/path/to/prompts/system_prompt_formalizer.md"

# Line 40: Semantic checker system prompt path
file_path = r"your/path/to/prompts/system_prompt_semantic.md"
```

Example:
```python
file_path = r"/home/user/zhugecunfu_pipeline/zhugecunfu/prompts/system_prompt_formalizer.md"
```

### 3. Update Input and Output File Paths

#### For Formalization (main_v1.py):

```python
# Line 53-55: Output file path for formalization results
output_file = r"your/path/to/output/lean_output.jsonl"

# Line 62: Input file path with natural language problems
file_path = r"your/path/to/input/problems.jsonl"
```

#### For Proving (prover_test.py):

```python
# Line 17: Input file path (should be the output from main_v1.py)
input_file = r"your/path/to/output/lean_output.jsonl"

# Line 38-40: Output file path for proving results
output_file = r"your/path/to/results/proof_results.jsonl"
```

## Input File Format

### For Formalization (main_v1.py input)

The input file should be in JSONL format with the following structure:

```json
{"id": "problem_id", "nl_problem": "Natural language math problem description"}
```

Example:
```json
{"id": "p001", "nl_problem": "Find the smallest x-coordinate of any point on the graph defined by r = cos(θ) + 1/2 in polar coordinates."}
```

### For Proving (prover_test.py input)

The prover expects the output from `main_v1.py`, which has the following format:

```json
{"id": "problem_id", "nl_problem": "Natural language problem", "formal": "Lean 4 code"}
```

## Running the Pipeline

### Step 1: Formalization

Run the formalization stage to convert natural language problems into Lean 4:

```bash
cd zhugecunfu
python main_v1.py
```

This will:
- Read natural language problems from the input file
- Generate Lean 4 formalizations
- Verify syntax using the Lean server
- Perform semantic checking
- Save results to the output file

### Step 2: Proving

After formalization completes, run the proving stage using the formalization output:

```bash
cd zhugecunfu
python prover_test.py
```

This will:
- Read the formalized Lean 4 problems
- Attempt to prove each problem (with 8 parallel attempts per problem)
- Verify proofs using the Lean server
- Save successful proofs to the output file

## Output Format

### Formalization Output (main_v1.py)

```json
{
  "id": "problem_id",
  "nl_problem": "Natural language problem",
  "formal": "Lean 4 formalized code"
}
```

### Proving Output (prover_test.py)

```json
{
  "success": true/false,
  "id": "problem_id",
  "informal": "Natural language problem",
  "lean_code": "Complete Lean 4 proof (if successful)"
}
```

## Configuration Parameters

### Formalization Parameters (main_v1.py)

```python
params['max_lean_generation'] = 5  # Maximum attempts to generate valid Lean code
params['max_full_check'] = 7       # Maximum full check iterations (syntax + semantic)
```

### Proving Parameters (prover_test.py)

```python
max_workers = 8  # Number of parallel proving workers
```

## Troubleshooting

### Common Issues

1. **Connection errors**: Ensure all model servers and Lean server are running
2. **Path errors**: Use absolute paths for all file locations
3. **Import errors**: Ensure all dependencies are installed and kimina_client is available
4. **Timeout errors**: Adjust timeout values in `model_calling.py` if needed

### Logs

Check console output for detailed progress and error messages during execution.

## Project Structure

```
zhugecunfu_pipeline/
├── zhugecunfu/
│   ├── main_v1.py                    # Formalization pipeline
│   ├── prover_test.py                # Proving pipeline
│   ├── model_calling.py              # LLM API wrapper
│   ├── lean_verifier.py              # Lean code verification
│   ├── question_formalizer_v1.py     # Formalization logic
│   ├── safe_writer.py                # Thread-safe JSONL writer
│   ├── prompts/
│   │   ├── system_prompt_formalizer.md
│   │   └── system_prompt_semantic.md
│   └── utils/
│       ├── text_extractor.py         # Text extraction utilities
│       ├── file_handler.py
│       └── logger_setup.py
├── README.md
└── requirements.txt
```

## License

[Add your license information here]

## Contributing

[Add contributing guidelines here]
