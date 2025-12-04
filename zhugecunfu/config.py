"""
Configuration file for Zhugecunfu Pipeline

Update the values below with your local settings before running the pipeline.
"""

import os
from pathlib import Path

# =============================================================================
# MODEL CONFIGURATION
# =============================================================================

# Formalizer Model (converts natural language to Lean 4)
FORMALIZER_MODEL_NAME = "your_local_model_name"  # e.g., "zhuge"
FORMALIZER_BASE_URL = "your_local_url"  # e.g., "http://localhost:8000/v1"

# Semantic Checker Model (validates semantic correspondence)
SEMANTIC_CHECKER_MODEL_NAME = "your_local_model_name"  
SEMANTIC_CHECKER_BASE_URL = "your_local_url"  

# Prover Model (generates Lean 4 proofs)
PROVER_MODEL_NAME = "your_local_model_name"  
PROVER_BASE_URL = "your_local_url"  

# Lean Server
LEAN_SERVER_URL = "your_local_lean_server_url"  # e.g., "http://localhost:8000"

# =============================================================================
# PROMPT PATHS
# =============================================================================

# Get the base directory (zhugecunfu folder)
BASE_DIR = Path(__file__).parent

# System prompts for models
FORMALIZER_PROMPT_PATH = BASE_DIR / "prompts" / "system_prompt_formalizer.md"
SEMANTIC_CHECKER_PROMPT_PATH = BASE_DIR / "prompts" / "system_prompt_semantic.md"

# =============================================================================
# FILE PATHS
# =============================================================================

# Input/Output directories (you can use absolute paths or relative to BASE_DIR)
DATA_DIR = Path("your/path/to/data")  # Update this to your data directory

# Formalization (main_v1.py) paths
FORMALIZATION_INPUT_FILE = DATA_DIR / "input" / "problems.jsonl"
FORMALIZATION_OUTPUT_DIR = DATA_DIR / "output"

# Proving (prover_test.py) paths
PROVING_INPUT_FILE = DATA_DIR / "output" / "lean_output.jsonl"  # Usually the output from formalization
PROVING_OUTPUT_DIR = DATA_DIR / "results"

# =============================================================================
# MODEL PARAMETERS
# =============================================================================

# Formalizer parameters
FORMALIZER_PARAMS = {
    'temperature': 0.6,
    'max_tokens': 16384,
    'top_p': 0.95,
    'top_k': 20,
}

# Semantic checker parameters
SEMANTIC_CHECKER_PARAMS = {
    'temperature': 0.5,
    'max_tokens': 16384,
    'top_p': 0.95,
    'top_k': 20,
    'use_json': True,
}

# Prover parameters
PROVER_PARAMS = {
    'temperature': 0.6,
    'max_tokens': 16384,
    'top_p': 0.95,
    'top_k': 20,
}

# =============================================================================
# PIPELINE PARAMETERS
# =============================================================================

# Formalization parameters
MAX_LEAN_GENERATION = 5  # Maximum attempts to generate valid Lean code
MAX_FULL_CHECK = 7  # Maximum full check iterations (syntax + semantic)

# Proving parameters
MAX_PROVING_ATTEMPTS = 2  # Maximum proving attempts per problem
PROVING_MAX_WORKERS = 8  # Number of parallel proving workers
PROVING_REPETITIONS = 8  # Number of times to repeat each problem for proving

# Formalization parallelization
FORMALIZATION_MAX_WORKERS = 100  # Number of parallel formalization workers
