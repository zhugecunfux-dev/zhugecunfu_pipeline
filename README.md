# Zhugecunfu Pipeline

A pipeline for auto-formalizing natural language mathematical problems into Lean 4 code and automatically proving them.

## Quick Start

1. **Install dependencies:** `pip install -r requirements.txt`
2. **Configure settings:** Edit `zhugecunfu/config.py` and update:
   - Model names and URLs (your local LLM servers)
   - Lean server URL
   - Input/output file paths
3. **Run formalization:** `cd zhugecunfu && python main_v1.py`
4. **Run proving:** `cd zhugecunfu && python prover_test.py`

See detailed instructions below for complete setup and configuration.

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

All configuration is centralized in **`zhugecunfu/config.py`**. Before running the pipeline, edit this single file to set up your environment.

### Configuration File: `zhugecunfu/config.py`

Open `zhugecunfu/config.py` and update the following sections:

#### 1. Model Configuration

Update the model names and URLs for your local LLM servers:

```python
# Formalizer Model (converts natural language to Lean 4)
FORMALIZER_MODEL_NAME = "your_local_model_name"  # e.g., "goedel"
FORMALIZER_BASE_URL = "your_local_url"  # e.g., "http://localhost:8000/v1"

# Semantic Checker Model (validates semantic correspondence)
SEMANTIC_CHECKER_MODEL_NAME = "your_local_model_name"  # e.g., "Qwen3"
SEMANTIC_CHECKER_BASE_URL = "your_local_url"  # e.g., "http://localhost:9000/v1"

# Prover Model (generates Lean 4 proofs)
PROVER_MODEL_NAME = "your_local_model_name"  # e.g., "kimina_72b"
PROVER_BASE_URL = "your_local_url"  # e.g., "http://localhost:10000/v1"

# Lean Server
LEAN_SERVER_URL = "your_local_lean_server_url"  # e.g., "http://localhost:15000"
```

#### 2. Prompt Paths (Usually No Change Needed)

The prompt paths are configured relative to the project directory. You typically don't need to change these unless you move the prompt files:

```python
# System prompts for models
FORMALIZER_PROMPT_PATH = BASE_DIR / "prompts" / "system_prompt_formalizer.md"
SEMANTIC_CHECKER_PROMPT_PATH = BASE_DIR / "prompts" / "system_prompt_semantic.md"
```

#### 3. Input and Output File Paths

Update the data directory and file paths:

```python
# Input/Output directories
DATA_DIR = Path("your/path/to/data")  # Update this to your data directory

# Formalization (main_v1.py) paths
FORMALIZATION_INPUT_FILE = DATA_DIR / "input" / "problems.jsonl"
FORMALIZATION_OUTPUT_DIR = DATA_DIR / "output"

# Proving (prover_test.py) paths
PROVING_INPUT_FILE = DATA_DIR / "output" / "lean_output.jsonl"
PROVING_OUTPUT_DIR = DATA_DIR / "results"
```

**Example configuration:**
```python
DATA_DIR = Path("/home/user/my_data")
FORMALIZATION_INPUT_FILE = DATA_DIR / "input" / "my_problems.jsonl"
```

#### 4. Pipeline Parameters (Optional)

You can adjust these parameters to control the pipeline behavior:

```python
# Formalization parameters
MAX_LEAN_GENERATION = 5  # Maximum attempts to generate valid Lean code
MAX_FULL_CHECK = 7  # Maximum full check iterations (syntax + semantic)

# Proving parameters
MAX_PROVING_ATTEMPTS = 2  # Maximum proving attempts per problem
PROVING_MAX_WORKERS = 8  # Number of parallel proving workers
PROVING_REPETITIONS = 8  # Number of times to repeat each problem for proving
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
#### Formalizer
```bash
git clone https://huggingface.co/Zhugecunfu/Zhugecunfu_Formalizer
```
#### Verifier
```bash
git clone https://huggingface.co/Zhugecunfu/Zhugecunfu_Critic
```
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

#### Prover
```bash
git clone https://huggingface.co/AI-MO/Kimina-Prover-72B
```
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

## Advanced Configuration

All pipeline parameters can be adjusted in `zhugecunfu/config.py`. See the "Pipeline Parameters" section in the config file for details.

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
│   ├── config.py                     # ⚙️ CONFIGURATION FILE (edit this!)
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

**Key File:** All configuration is centralized in `zhugecunfu/config.py` - this is the only file you need to edit to set up the pipeline.


