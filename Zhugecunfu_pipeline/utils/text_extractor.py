"""Utilities for extracting text from responses."""
import re
import json
from typing import Optional
import logging
from typing import Dict, Any, Optional, Tuple

logger = logging.getLogger(__name__)

def extract_text(response, start_tag, end_tag) -> str:
    
    rtn = response
    if not isinstance(response,str): return ""
    i = rtn.find(start_tag)
    if i == -1: return ""
    rtn = rtn[i+len(start_tag):]
    i = rtn.find(end_tag)
    if i == -1: return ""
    rtn = rtn[:i]

    return rtn


def extract_thinking(response: str) -> str:
    """Extract thinking content between <think> tags."""
    if not isinstance(response, str):
        return ""
    
    start_tag = "<think>"
    end_tag = "</think>"
    
    i = response.find(start_tag)
    if i == -1:
        return ""
    
    j = response.find(end_tag, i + len(start_tag))
    if j == -1:
        return ""
    
    return response[i + len(start_tag): j]


def extract_lean_code(response_text: str) -> str:
    """
    Extract Lean code from the model's response.
    Tries multiple extraction methods in order of preference.
    
    New model format: <think>...</think>```lean4\ncode\n```
    """
    if not response_text:
        return ""
    
    # Method 1: Extract from </think> tag onwards with markdown code blocks
    lean_code = _extract_from_think_tag_with_markdown(response_text)
    if lean_code:
        return lean_code
    
    # Method 2: Extract from </think> tag onwards (any code)
    lean_code = _extract_from_think_tag(response_text)
    if lean_code:
        return lean_code
    
    # Method 3: Extract from code blocks (```)
    lean_code = _extract_from_code_blocks(response_text)
    if lean_code:
        return lean_code
    
    # Method 4: Find any import Mathlib statement
    lean_code = _extract_from_import(response_text)
    if lean_code:
        return lean_code
    
    logger.warning("Could not extract Lean code using any method")
    return ""


def _extract_from_think_tag_with_markdown(response_text: str) -> str:
    """
    Extract Lean code from markdown blocks after </think> tag.
    Handles format: </think>```lean4\ncode\n```
    """
    # Find content after </think>
    think_match = re.search(r'</think>\s*(.+)', response_text, flags=re.DOTALL | re.IGNORECASE)
    if not think_match:
        return ""
    
    content_after_think = think_match.group(1)
    
    # Look for markdown code blocks after </think>
    # Pattern 1: ```lean4 or ```lean
    patterns = [
        r'```lean4\s*(.*?)\s*```',
        r'```lean\s*(.*?)\s*```',
    ]
    
    for pattern in patterns:
        match = re.search(pattern, content_after_think, flags=re.DOTALL)
        if match:
            code = match.group(1).strip()
            logger.debug("Extracted code from markdown block after </think>")
            return code
    
    # Pattern 2: Generic ``` block after </think>
    generic_match = re.search(r'```\s*(.*?)\s*```', content_after_think, flags=re.DOTALL)
    if generic_match:
        potential_code = generic_match.group(1).strip()
        # Check if it looks like Lean code
        if _looks_like_lean(potential_code):
            logger.debug("Extracted Lean-like code from generic markdown block after </think>")
            return potential_code
    
    return ""


def _extract_from_think_tag(response_text: str) -> str:
    """Extract Lean code after </think> tag (without markdown)."""
    m = re.search(r'</think>(.*)', response_text, flags=re.DOTALL | re.IGNORECASE)
    if not m:
        return ""
    
    content_after_think = m.group(1).strip()
    
    # Remove markdown code block delimiters if present
    content_after_think = re.sub(r'^```(?:lean4|lean)?\s*', '', content_after_think)
    content_after_think = re.sub(r'\s*```$', '', content_after_think)
    content_after_think = content_after_think.strip()
    
    # Look for import Mathlib
    mathlib_match = re.search(r'\bimport\s+Mathlib\b.*', content_after_think, flags=re.DOTALL)
    if mathlib_match:
        extracted_code = mathlib_match.group(0).strip()
        logger.debug("Extracted code after </think> (with import Mathlib)")
        return extracted_code
    
    # If no import Mathlib, but looks like Lean code, return it
    if _looks_like_lean(content_after_think):
        logger.debug("Extracted Lean-like code after </think>")
        return content_after_think
    
    return ""


def _extract_from_code_blocks(response_text: str) -> str:
    """
    Extract Lean code from markdown code blocks (```lean4, ```lean or ```).
    Looks for code blocks that contain 'import Mathlib' or look like Lean.
    """
    # Pattern 1: ```lean4 ... ```
    lean4_blocks = re.findall(
        r'```lean4\s*(.*?)```', 
        response_text, 
        flags=re.DOTALL | re.IGNORECASE
    )
    
    # Pattern 2: ```lean ... ```
    lean_blocks = re.findall(
        r'```lean\s*(.*?)```', 
        response_text, 
        flags=re.DOTALL | re.IGNORECASE
    )
    
    # Pattern 3: ``` ... ``` (without language specifier)
    generic_blocks = re.findall(
        r'```\s*(.*?)```', 
        response_text, 
        flags=re.DOTALL
    )
    
    # Try lean4 blocks first, then lean, then generic
    all_blocks = lean4_blocks + lean_blocks + generic_blocks
    
    # Find the first block that contains 'import Mathlib'
    for block in all_blocks:
        if 'import' in block.lower() and 'mathlib' in block.lower():
            # Extract from 'import Mathlib' onwards
            import_match = re.search(
                r'\bimport\s+Mathlib\b.*', 
                block, 
                flags=re.DOTALL | re.IGNORECASE
            )
            if import_match:
                logger.debug("Extracted code from markdown block (with import)")
                return import_match.group(0).strip()
    
    # If no import found, try blocks that look like Lean
    for block in all_blocks:
        if _looks_like_lean(block):
            logger.debug("Extracted Lean-like code from markdown block")
            return block.strip()
    
    return ""


def _extract_from_import(response_text: str) -> str:
    """
    Fallback: Extract everything starting from 'import Mathlib'.
    This is the most permissive method.
    """
    # Find 'import Mathlib' anywhere in the text
    import_match = re.search(
        r'\bimport\s+Mathlib\b.*', 
        response_text, 
        flags=re.DOTALL | re.IGNORECASE
    )
    
    if not import_match:
        return ""
    
    code = import_match.group(0).strip()
    
    # Clean up: remove markdown artifacts if present
    # Remove trailing ``` if present
    code = re.sub(r'```\s*$', '', code, flags=re.MULTILINE)
    
    logger.debug("Extracted code using import Mathlib fallback")
    return code.strip()


def _looks_like_lean(text: str) -> bool:
    """
    Check if text looks like Lean code.
    Uses heuristics based on common Lean keywords.
    """
    if not text or len(text) < 10:
        return False
    
    # Check for common Lean keywords
    lean_keywords = [
        'theorem', 'lemma', 'def', 'example', 
        'import', 'open', 'namespace', 'variable',
        'sorry', 'by', ':=', '⊢', 'Type', 'Prop',
        'have', 'show', 'calc', 'match'
    ]
    
    text_lower = text.lower()
    keyword_count = sum(1 for kw in lean_keywords if kw.lower() in text_lower)
    
    # Also check for Lean-specific patterns
    has_type_annotation = ':' in text and ('ℕ' in text or 'ℝ' in text or 'Type' in text or 'Prop' in text)
    has_proof = 'by' in text_lower or ':=' in text or 'sorry' in text_lower
    
    # If it has at least 2 Lean keywords, or type annotations with proof, probably Lean code
    return keyword_count >= 2 or (has_type_annotation and has_proof)


def extract_lean_code_robust(response_text: str) -> str:
    """
    Robust Lean code extractor with multiple fallback strategies.
    Returns the first successfully extracted code.
    
    Extraction order:
    1. Code in markdown blocks after </think> tag (NEW - handles ```lean4)
    2. Code after </think> tag (with or without markdown)
    3. Code inside ```lean4, ```lean or ``` blocks
    4. Everything starting from 'import Mathlib'
    """
    return extract_lean_code(response_text)


def read_prompt_file(file_path: str) -> str:
    """Read a prompt file as text."""
    with open(file_path, 'r', encoding='utf-8') as f:
        return f.read()
    

def _parse_json_response(response: str) -> Optional[Dict]:
    """
    Parse JSON from response, handling various formats.
    
    Args:
        response: Raw response string
        
    Returns:
        Parsed JSON dict or None if parsing fails
    """
    if not response:
        return None
    
    response = response.replace("\\", "\\\\")

    # Try direct JSON parse
    try:
        return json.loads(response)
    except json.JSONDecodeError:
        pass
    

    # Try to extract JSON from markdown code blocks
    json_pattern = r'```(?:json)?\s*(\{.*?\})\s*```'
    match = re.search(json_pattern, response, re.DOTALL)
    if match:
        try:
            return json.loads(match.group(1))
        except json.JSONDecodeError:
            pass
    
    # Try to find JSON object in text
    json_obj_pattern = r'\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}'
    matches = re.finditer(json_obj_pattern, response, re.DOTALL)
    for match in matches:
        try:
            return json.loads(match.group(0))
        except json.JSONDecodeError:
            continue
    
    logger.warning(f"Could not parse JSON from response: {response}...")
    return None