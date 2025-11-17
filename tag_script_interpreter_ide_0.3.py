"""
TagScript Interpreter + Simple GUI IDE (patched, non-freezing, .tag-only, with bring_net)
File: tag_script_interpreter_ide.py

Run: python tag_script_interpreter_ide.py

Features:
- Non-blocking Tkinter IDE (interpreter runs in a worker thread; GUI communicates via queues)
- TagScript parsing (forgiving, not strict XML)
- Safe expression evaluator (AST-based)
- .tag-only script/module support (open/save defaults to .tag)
- load local .tag modules via <bring module="name" /> (looks in CWD and stdlib_path)
- download remote .tag modules via <bring_net url="https://raw.../module.tag" />
  OR <bring_net name="module"> which will be fetched from the default repo:
  https://raw.githubusercontent.com/TheServer-lab/tagscriptonlinelibs/main/{name}.tag
- downloaded modules cached under stdlib_path/net_cache/
- extracted <doit name="..."> functions from tag modules are exposed as Python-callable wrappers

Author: integrated patch for user
"""

import ast
import operator
import importlib
import importlib.util
import os
import queue
import re
import threading
import time
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk
import urllib.request
import urllib.parse
import urllib.error

# -----------------------------
# TSNode (AST-like) for TagScript
# -----------------------------
class TSNode:
    def __init__(self, tag, attrib=None, text=None, children=None):
        self.tag = tag
        self.attrib = attrib or {}
        self.text = text or ''
        self.children = children or []

    def __repr__(self):
        return f"<TSNode {self.tag} attrib={self.attrib} text={repr(self.text)} children={len(self.children)}>"

# -----------------------------
# Safe expression evaluator
# -----------------------------
class SafeEvaluator:
    """
    Minimal safe evaluator using AST. Only supports expressions (no calls/attributes).
    """

    KEYWORD_MAP = {'both': 'and', 'either': 'or', 'notreally': 'not'}

    ALLOWED_NODES = (
        ast.Expression, ast.BinOp, ast.UnaryOp, ast.BoolOp, ast.Compare,
        ast.Name, ast.Load, ast.Constant, ast.List, ast.Tuple, ast.Dict,
        ast.Subscript, ast.Slice
    )

    ALLOWED_BINOPS = {
        ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul,
        ast.Div: operator.truediv, ast.Mod: operator.mod, ast.Pow: operator.pow,
        ast.FloorDiv: operator.floordiv
    }

    ALLOWED_UNARY = {ast.UAdd: operator.pos, ast.USub: operator.neg, ast.Not: operator.not_}

    SAFE_BUILTINS = {'len': len, 'int': int, 'float': float, 'str': str, 'bool': bool,
                     'min': min, 'max': max, 'abs': abs, 'range': range, 'list': list,
                     'dict': dict, 'sorted': sorted}

    def __init__(self, env=None, extras=None):
        # env: TagScript variables, extras: safe modules like math/time
        self.env = env or {}
        self.extras = extras or {}

    def _preprocess(self, s: str) -> str:
        out = str(s)
        for k, v in self.KEYWORD_MAP.items():
            out = re.sub(rf'\b{k}\b', v, out)
        return out

    def eval(self, expr):
        if expr is None:
            return None
        if isinstance(expr, (int, float, bool, list, dict, tuple, str)):
            return expr
        s = self._preprocess(str(expr).strip())
        try:
            node = ast.parse(s, mode='eval')
        except Exception as e:
            raise RuntimeError(f"Expression parse error: {e} -- '{s}'")
        return self._eval_node(node.body)

    def _eval_node(self, node):
        if not isinstance(node, self.ALLOWED_NODES):
            raise RuntimeError(f"Disallowed element: {type(node).__name__}")

        if isinstance(node, ast.Constant):
            return node.value

        if isinstance(node, ast.Name):
            name = node.id
            if name in self.env:
                return self.env[name]
            if name in self.extras:
                return self.extras[name]
            if name in self.SAFE_BUILTINS:
                return self.SAFE_BUILTINS[name]
            raise RuntimeError(f"Unknown name '{name}'")

        if isinstance(node, ast.BinOp):
            left = self._eval_node(node.left)
            right = self._eval_node(node.right)
            op_type = type(node.op)
            if op_type in self.ALLOWED_BINOPS:
                return self.ALLOWED_BINOPS[op_type](left, right)
            raise RuntimeError(f"Operator {op_type} not allowed")

        if isinstance(node, ast.UnaryOp):
            operand = self._eval_node(node.operand)
            op_type = type(node.op)
            if op_type in self.ALLOWED_UNARY:
                return self.ALLOWED_UNARY[op_type](operand)
            raise RuntimeError(f"Unary op {op_type} not allowed")

        if isinstance(node, ast.BoolOp):
            if isinstance(node.op, ast.And):
                return all(self._eval_node(v) for v in node.values)
            if isinstance(node.op, ast.Or):
                return any(self._eval_node(v) for v in node.values)
            raise RuntimeError("Unsupported boolean op")

        if isinstance(node, ast.Compare):
            left = self._eval_node(node.left)
            for op, comp in zip(node.ops, node.comparators):
                right = self._eval_node(comp)
                if isinstance(op, ast.Eq):
                    ok = (left == right)
                elif isinstance(op, ast.NotEq):
                    ok = (left != right)
                elif isinstance(op, ast.Gt):
                    ok = (left > right)
                elif isinstance(op, ast.Lt):
                    ok = (left < right)
                elif isinstance(op, ast.GtE):
                    ok = (left >= right)
                elif isinstance(op, ast.LtE):
                    ok = (left <= right)
                else:
                    raise RuntimeError("Unsupported comparison op")
                if not ok:
                    return False
                left = right
            return True

        if isinstance(node, (ast.List, ast.Tuple)):
            return [self._eval_node(e) for e in node.elts]

        if isinstance(node, ast.Dict):
            keys = [self._eval_node(k) for k in node.keys]
            vals = [self._eval_node(v) for v in node.values]
            return dict(zip(keys, vals))

        if isinstance(node, ast.Subscript):
            val = self._eval_node(node.value)
            sl = node.slice
            # handle slice vs index differences across Python versions
            if isinstance(sl, ast.Slice):
                lower = self._eval_node(sl.lower) if sl.lower else None
                upper = self._eval_node(sl.upper) if sl.upper else None
                return val[lower:upper]
            else:
                idx = self._eval_node(sl)
                return val[idx]

        raise RuntimeError(f"Unsupported node: {type(node).__name__}")

# -----------------------------
# TagScript parser (forgiving, not strict XML)
# -----------------------------
_TAG_RE = re.compile(r'<\s*(/)?\s*([a-zA-Z0-9_.-]+)([^>]*)>', re.DOTALL)
_ATTR_RE = re.compile(r'([a-zA-Z_:][-a-zA-Z0-9_:.]*)\s*=\s*("(?:[^"]*)"|\'(?:[^\']*)\')')

def parse_tagscript(source: str) -> TSNode:
    # Strip HTML-style comments first so they don't appear as text nodes.
    source = re.sub(r'<!--.*?-->', '', source, flags=re.DOTALL)
    pos = 0
    root = TSNode('root', {}, '')
    stack = [root]
    length = len(source)
    while pos < length:
        m = _TAG_RE.search(source, pos)
        if not m:
            text = source[pos:]
            if text:
                stack[-1].children.append(TSNode('#text', {}, text))
            break
        start, end = m.span()
        if start > pos:
            text = source[pos:start]
            if text:
                stack[-1].children.append(TSNode('#text', {}, text))
        closing = bool(m.group(1))
        tagname = m.group(2)
        attrtext = m.group(3).strip()
        # simplistic self-close detection
        self_close = attrtext.endswith('/') or source[end-2:end] == '/>'
        attrib = {}
        for am in _ATTR_RE.finditer(attrtext):
            aname = am.group(1)
            av = am.group(2)
            if (av.startswith('"') and av.endswith('"')) or (av.startswith("'") and av.endswith("'")):
                av = av[1:-1]
            attrib[aname] = av
        pos = end
        if closing:
            if len(stack) == 1:
                continue
            for i in range(len(stack)-1, 0, -1):
                if stack[i].tag.lower() == tagname.lower():
                    while len(stack)-1 >= i:
                        stack.pop()
                    break
            continue
        node = TSNode(tagname, attrib, '')
        stack[-1].children.append(node)
        if not self_close:
            stack.append(node)
    _coalesce_text(root)
    return root

def _coalesce_text(node: TSNode):
    if not node.children:
        return
    new_children = []
    buf = []
    for ch in node.children:
        if ch.tag == '#text':
            buf.append(ch.text)
        else:
            if buf:
                t = ''.join(buf)
                if t != '':
                    new_children.append(TSNode('#text', {}, t))
                buf = []
            new_children.append(ch)
    if buf:
        t = ''.join(buf)
        if t != '':
            new_children.append(TSNode('#text', {}, t))
    node.children = new_children
    for ch in node.children:
        if ch.tag != '#text':
            _coalesce_text(ch)

# -----------------------------
# Interpreter (supports .tag modules and bring_net)
# -----------------------------
class TagScriptRuntimeError(Exception):
    pass

class _ReturnSignal:
    def __init__(self, value):
        self.value = value

class TagScriptInterpreter:
    def __init__(self, input_fn=None, output_fn=None, stdlib_path='stdlib'):
        self.env = {}
        self.consts = {}
        self.functions = {}
        # modules: mapping name -> dict(callable/values)
        self.modules = {}
        self.input_fn = input_fn or (lambda prompt=None: input(prompt or '> '))
        self.output_fn = output_fn or print
        self.stop_requested = False
        self.last_exception = None
        self.stdlib_path = stdlib_path
        # ensure stdlib_path exists
        try:
            os.makedirs(self.stdlib_path, exist_ok=True)
        except Exception:
            pass
        # extras for SafeEvaluator (math/time)
        try:
            import math, time as _t
            self.extra_names = {'math': math, 'time': _t}
        except Exception:
            self.extra_names = {}

    def reset(self):
        self.env.clear()
        self.consts.clear()
        self.functions.clear()
        # keep loaded modules across resets so downloaded modules persist for session
        # self.modules.clear()
        self.stop_requested = False
        self.last_exception = None

    # -----------------
    # local/python/stdlib loader (keeps .tag-first behavior)
    # -----------------
    def load_stdlib(self, name):
        """
        Load a module by name:
         - try python package stdlib.name first (backwards compatibility)
         - then try loading name.tag from CWD and stdlib_path
        Returns a dict of exported callables/values.
        """
        # try python package first
        try:
            specname = f"stdlib.{name}"
            mod = importlib.import_module(specname)
            if hasattr(mod, 'module'):
                self.modules[name] = mod.module
                return mod.module
            else:
                d = {k: getattr(mod, k) for k in dir(mod) if not k.startswith('_')}
                self.modules[name] = d
                return d
        except ModuleNotFoundError:
            pass
        except Exception:
            # other import error: don't crash; try tag module next
            pass

        # try .tag file in CWD or stdlib_path
        tag_filename = f"{name}.tag"
        candidates = [os.path.join(os.getcwd(), tag_filename),
                      os.path.join(self.stdlib_path, tag_filename)]
        for path in candidates:
            if os.path.exists(path):
                return self._load_tag_module_from_path(path, name)

        raise ModuleNotFoundError(f"Module '{name}' not found (python package or .tag)")

    def _load_tag_module_from_path(self, path, name_hint=None):
        """
        Parse a .tag file and extract <doit name="..."> functions into a dict.
        """
        with open(path, 'r', encoding='utf-8') as f:
            src = f.read()
        tree = parse_tagscript(src)
        moddict = {}
        # Search for <module> wrapper or top-level <doit>
        nodes_to_search = []
        for ch in tree.children:
            if ch.tag.lower() == 'module':
                nodes_to_search.extend(ch.children)
            else:
                nodes_to_search.append(ch)
        for ch in nodes_to_search:
            if ch.tag.lower() == 'doit':
                fname = ch.attrib.get('name')
                args_attr = ch.attrib.get('args', '')
                args_list = [a.strip() for a in args_attr.split(',') if a.strip()] if args_attr else []
                wrapper = self._make_wrapper_for_node(ch, args_list)
                if fname:
                    moddict[fname] = wrapper
        module_name = name_hint or os.path.splitext(os.path.basename(path))[0]
        self.modules[module_name] = moddict
        return moddict

    def _make_wrapper_for_node(self, fn_node, fn_args):
        # return a Python callable that executes the TSNode block with copied env
        def wrapper(*call_args, __fn_node=fn_node, __fn_args=list(fn_args)):
            backup_env = dict(self.env)
            try:
                # bind positional args into env
                for i, an in enumerate(__fn_args):
                    self.env[an] = call_args[i] if i < len(call_args) else None
                res = self._exec_block(__fn_node)
                if isinstance(res, _ReturnSignal):
                    return res.value
                return None
            finally:
                # restore environment
                self.env = backup_env
        return wrapper

    # -----------------
    # network loader (bring_net)
    # -----------------
    def load_stdlib_net(self, name_or_url):
        """
        Download a .tag module from a raw URL or from the default repo:
         - if name_or_url looks like a full URL (http/https) -> fetch it directly
         - otherwise build URL: https://raw.githubusercontent.com/TheServer-lab/tagscriptonlinelibs/main/{name}.tag
        Cache downloaded content under stdlib_path/net_cache/{safe_name}.tag
        Returns module dict (doit wrappers).
        """
        s = str(name_or_url).strip()
        if s.lower().startswith('http://') or s.lower().startswith('https://'):
            url = s
            safe_basename = os.path.basename(urllib.parse.urlparse(url).path) or 'downloaded.tag'
            if not safe_basename.lower().endswith('.tag'):
                safe_basename += '.tag'
        else:
            name = s
            url = f"https://raw.githubusercontent.com/TheServer-lab/tagscriptonlinelibs/main/{urllib.parse.quote(name)}.tag"
            safe_basename = f"{name}.tag"

        cache_dir = os.path.join(self.stdlib_path, 'net_cache')
        os.makedirs(cache_dir, exist_ok=True)
        cache_path = os.path.join(cache_dir, safe_basename)

        # If cached, try to load from cache
        if os.path.exists(cache_path):
            try:
                return self._load_tag_module_from_path(cache_path, os.path.splitext(safe_basename)[0])
            except Exception:
                # attempt re-download if cache parsing failed
                pass

        # download
        try:
            with urllib.request.urlopen(url, timeout=12) as resp:
                # urllib in some Python versions doesn't have .status - be defensive
                status = getattr(resp, 'status', None)
                if status is not None and status != 200:
                    raise RuntimeError(f"HTTP {status} while fetching {url}")
                data = resp.read()
                text = data.decode('utf-8', errors='replace')
        except urllib.error.URLError as e:
            raise RuntimeError(f"Failed to download module from {url}: {e}")
        except Exception as e:
            raise RuntimeError(f"Failed to download module from {url}: {e}")

        # write to cache
        try:
            with open(cache_path, 'w', encoding='utf-8') as fh:
                fh.write(text)
        except Exception:
            # ignore caching failure, but continue with in-memory parse
            pass

        # parse and extract functions
        tree = parse_tagscript(text)
        moddict = {}
        nodes_to_search = []
        for ch in tree.children:
            if ch.tag.lower() == 'module':
                nodes_to_search.extend(ch.children)
            else:
                nodes_to_search.append(ch)
        for ch in nodes_to_search:
            if ch.tag.lower() == 'doit':
                fname = ch.attrib.get('name')
                args_attr = ch.attrib.get('args', '')
                args_list = [a.strip() for a in args_attr.split(',') if a.strip()] if args_attr else []
                wrapper = self._make_wrapper_for_node(ch, args_list)
                if fname:
                    moddict[fname] = wrapper
        module_name = os.path.splitext(safe_basename)[0]
        self.modules[module_name] = moddict
        return moddict

    # -----------------
    # parsing / execution
    # -----------------
    def parse(self, source):
        try:
            return parse_tagscript(source)
        except Exception as e:
            raise TagScriptRuntimeError(f"Parse error: {e}")

    def _interp_text(self, text):
        if text is None:
            return ''
        res = str(text)

        # handle {{ expr }} interpolation using SafeEvaluator
        def repl(m):
            expr = m.group(1).strip()
            try:
                ev = SafeEvaluator(env=self.env, extras=self.extra_names)
                val = ev.eval(expr)
                return str(val)
            except Exception:
                return '{{' + expr + '}}'

        res = re.sub(r'\{\{\s*(.*?)\s*\}\}', repl, res)
        # simple {var} replacement (legacy)
        for k, v in list(self.env.items()):
            try:
                res = res.replace(f"{{{k}}}", str(v))
            except Exception:
                pass
        return res

    def _eval_attr(self, attr_value):
        if attr_value is None:
            return None
        s = str(attr_value).strip()
        if (s.startswith('"') and s.endswith('"')) or (s.startswith("'") and s.endswith("'")):
            # quoted string: interpolate inside
            return self._interp_text(s[1:-1])
        ev = SafeEvaluator(env=self.env, extras=self.extra_names)
        return ev.eval(s)

    def run(self, root: TSNode):
        node = root
        # find <page>/<start> if present
        if root.tag.lower() == 'root':
            page = None
            for ch in root.children:
                if ch.tag.lower() == 'page':
                    page = ch
                    break
            node = page or root
            for ch in node.children:
                if ch.tag.lower() == 'start':
                    node = ch
                    break
        return self._exec_block(node)

    def _exec_block(self, node: TSNode):
        result = None
        for child in list(node.children):
            if self.stop_requested:
                break
            if child.tag == '#text':
                if child.text.strip():
                    self.output_fn(self._interp_text(child.text))
                continue
            result = self._exec_node(child)
            if isinstance(result, _ReturnSignal):
                return result
        return result

    def _exec_node(self, node: TSNode):
        tag = node.tag.lower()

        # -- basic tags --
        if tag == 'write':
            txt = None
            if node.children and node.children[0].tag == '#text':
                txt = node.children[0].text
            else:
                txt = node.text
            self.output_fn(self._interp_text(txt or ''))
            return None

        if tag == 'take':
            prompt = node.attrib.get('prompt') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text)
            return self.input_fn(self._interp_text(prompt or ''))

        if tag == 'letssay':
            name = node.attrib.get('name')
            if not name:
                content = (node.children[0].text.strip() if node.children and node.children[0].tag == '#text' else (node.text or '').strip())
                if '=' in content:
                    lhs, rhs = content.split('=', 1)
                    name = lhs.strip()
                    val = self._eval_attr(rhs.strip())
                    self.env[name] = val
                    return None
                raise TagScriptRuntimeError('letssay missing name')
            if 'value' in node.attrib:
                val = self._eval_attr(node.attrib['value'])
            elif node.children and node.children[0].tag == 'take':
                val = self._exec_node(node.children[0])
            elif node.children and node.children[0].tag == '#text':
                val = self._interp_text(node.children[0].text)
            else:
                val = None
            self.env[name] = val
            return None

        if tag == 'fixed':
            name = node.attrib.get('name')
            if not name:
                raise TagScriptRuntimeError('fixed requires name attribute')
            if 'value' in node.attrib:
                v = self._eval_attr(node.attrib['value'])
            else:
                v = node.text or ''
            self.consts[name] = v
            self.env[name] = v
            return None

        if tag == 'isnow':
            name = node.attrib.get('name')
            if not name:
                content = (node.children[0].text.strip() if node.children and node.children[0].tag == '#text' else (node.text or '').strip())
                if '=' in content:
                    lhs, rhs = content.split('=', 1)
                    name = lhs.strip()
                    val = self._eval_attr(rhs.strip())
                else:
                    raise TagScriptRuntimeError('isnow bad assignment')
            else:
                val = self._eval_attr(node.attrib['value']) if 'value' in node.attrib else None
            if name in self.consts:
                raise TagScriptRuntimeError('Cannot reassign fixed constant')
            self.env[name] = val
            return None

        if tag in ('whentrue', 'if'):
            cond = node.attrib.get('value') or node.attrib.get('condition') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text or '')
            ev = SafeEvaluator(env=self.env, extras=self.extra_names)
            try:
                ok = bool(ev.eval(cond))
            except Exception as e:
                raise TagScriptRuntimeError(f'Condition eval error: {e}')
            if ok:
                return self._exec_block(node)
            return None

        if tag in ('whentruealso', 'elif'):
            cond = node.attrib.get('value') or node.attrib.get('condition') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text or '')
            ev = SafeEvaluator(env=self.env, extras=self.extra_names)
            try:
                ok = bool(ev.eval(cond))
            except Exception as e:
                raise TagScriptRuntimeError(f'Condition eval error: {e}')
            if ok:
                return self._exec_block(node)
            return None

        if tag in ('otherwise', 'else'):
            return self._exec_block(node)

        if tag in ('aslong', 'while'):
            cond = node.attrib.get('value') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text or '')
            ev = SafeEvaluator(env=self.env, extras=self.extra_names)
            while True:
                if self.stop_requested:
                    break
                try:
                    ok = bool(ev.eval(cond))
                except Exception as e:
                    raise TagScriptRuntimeError(f'While cond eval error: {e}')
                if not ok:
                    break
                # yield a little to allow GUI to process queue and to avoid CPU spin
                time.sleep(0.001)
                res = self._exec_block(node)
                if isinstance(res, _ReturnSignal):
                    return res
            return None

        if tag in ('foreach', 'for'):
            item_name = node.attrib.get('item', 'item')
            iterable = node.attrib.get('in') or node.attrib.get('inlist') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text)
            ev = SafeEvaluator(env=self.env, extras=self.extra_names)
            it = ev.eval(iterable)
            if hasattr(it, '__iter__'):
                for val in it:
                    if self.stop_requested:
                        break
                    self.env[item_name] = val
                    res = self._exec_block(node)
                    if isinstance(res, _ReturnSignal):
                        return res
                    time.sleep(0.0005)
                return None
            raise TagScriptRuntimeError('foreach: object not iterable')

        if tag == 'additem':
            lstname = node.attrib.get('list')
            item = node.attrib.get('item')
            if lstname is None:
                raise TagScriptRuntimeError('additem missing list attr')
            val = self._eval_attr(item)
            lst = self.env.get(lstname)
            if lst is None:
                lst = []
                self.env[lstname] = lst
            lst.append(val)
            return None

        if tag == 'put':
            mapname = node.attrib.get('map') or node.attrib.get('dict')
            if not mapname:
                raise TagScriptRuntimeError('put missing map/dict attr')
            key = node.attrib.get('key')
            val_attr = node.attrib.get('value')
            val = self._eval_attr(val_attr)
            mp = self.env.get(mapname)
            if mp is None:
                mp = {}
                self.env[mapname] = mp
            mp[self._eval_attr(key)] = val
            return None

        if tag == 'getfrom':
            mapname = node.attrib.get('map') or node.attrib.get('dict')
            key = node.attrib.get('key')
            default = node.attrib.get('default')
            mp = self.env.get(mapname, {})
            return mp.get(self._eval_attr(key), self._eval_attr(default))

        if tag == 'doit':
            name = node.attrib.get('name')
            args = node.attrib.get('args', '')
            args = [a.strip() for a in args.split(',') if a.strip()] if args else []
            self.functions[name] = (node, args)
            return None

        if tag == 'useit':
            callname = node.attrib.get('call') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text)
            with_arg = node.attrib.get('with')
            args = []
            if with_arg:
                parts = [p.strip() for p in with_arg.split(',') if p.strip()]
                ev = SafeEvaluator(env=self.env, extras=self.extra_names)
                for p in parts:
                    args.append(ev.eval(p))
            # module function call like mod.func
            if callname and '.' in callname:
                modname, fname = callname.split('.', 1)
                mod = self.modules.get(modname) or self.load_stdlib(modname)
                fn = None
                if isinstance(mod, dict):
                    fn = mod.get(fname)
                else:
                    fn = getattr(mod, fname, None)
                if fn is None:
                    raise TagScriptRuntimeError(f'Module function not found: {fname} in {modname}')
                return fn(*args)
            # local function defined by doit
            if callname in self.functions:
                fn_node, fn_args = self.functions[callname]
                backup = dict(self.env)
                try:
                    for i, a in enumerate(fn_args):
                        self.env[a] = args[i] if i < len(args) else None
                    res = self._exec_block(fn_node)
                    if isinstance(res, _ReturnSignal):
                        return res.value
                finally:
                    self.env = backup
                return None
            # direct callable in env
            fn = self.env.get(callname)
            if callable(fn):
                return fn(*args)
            raise TagScriptRuntimeError(f'Function not found: {callname}')

        if tag == 'giveback':
            if 'value' in node.attrib:
                v = self._eval_attr(node.attrib.get('value'))
            elif node.children and node.children[0].tag == '#text':
                v = self._interp_text(node.children[0].text)
            else:
                v = None
            return _ReturnSignal(v)

        if tag == 'maybework':
            try:
                return self._exec_block(node)
            except Exception as e:
                self.last_exception = e
                return None

        if tag == 'ifbroken':
            name = node.attrib.get('as') or 'err'
            if self.last_exception is not None:
                self.env[name] = self.last_exception
                return self._exec_block(node)
            return None

        if tag == 'breakit':
            msg = node.attrib.get('value') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text or 'Error')
            raise TagScriptRuntimeError(msg)

        # file ops
        if tag == 'fileopen':
            path = node.attrib.get('path')
            mode = node.attrib.get('mode', 'r')
            save = node.attrib.get('save')
            f = open(path, mode, encoding='utf-8')
            if save:
                self.env[save] = f
            return f

        if tag == 'fileread':
            fref = node.attrib.get('file')
            save = node.attrib.get('save')
            f = self.env.get(fref) if fref else None
            if f is None and fref:
                f = open(fref, 'r', encoding='utf-8')
            content = f.read() if f else ''
            if save:
                self.env[save] = content
            return content

        if tag == 'filewrite':
            fref = node.attrib.get('file')
            text = node.attrib.get('text') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text or '')
            f = self.env.get(fref)
            if callable(f):
                f(text)
            elif hasattr(f, 'write'):
                f.write(str(text))
            else:
                with open(fref, 'w', encoding='utf-8') as fh:
                    fh.write(str(text))
            return None

        if tag == 'fileclose':
            fref = node.attrib.get('file')
            f = self.env.get(fref)
            if hasattr(f, 'close'):
                f.close()
            return None

        # bring (local .tag or python stdlib)
        if tag == 'bring':
            modname = node.attrib.get('module') or node.attrib.get('name') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text)
            if modname is None:
                raise TagScriptRuntimeError('bring missing module name')
            modname = str(modname).strip()
            try:
                m = self.load_stdlib(modname)
                return m
            except Exception as e:
                raise TagScriptRuntimeError(f'Error loading module {modname}: {e}')

        # bring_net (download from raw github or default repo)
        if tag == 'bring_net' or tag == 'bringnet':
            # accept url= or name= or module=
            url = node.attrib.get('url') or node.attrib.get('module') or node.attrib.get('name') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text)
            if url is None:
                raise TagScriptRuntimeError('bring_net missing url/name')
            url = str(url).strip()
            try:
                m = self.load_stdlib_net(url)
                return m
            except Exception as e:
                raise TagScriptRuntimeError(f'Error loading network module {url}: {e}')

        # fallback: unknown tag -> execute children
        return self._exec_block(node)

# -----------------------------
# Tkinter IDE (non-freezing)
# -----------------------------
class TagScriptIDE(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title('TagScript IDE')
        self.geometry('1000x700')
        self.protocol('WM_DELETE_WINDOW', self._on_close)

        # queues
        self.run_queue = queue.Queue()   # interpreter -> GUI
        self.run_thread = None
        self.current_file = None

        self._make_widgets()

        # interpreter created with input_fn that uses request_input()
        # default stdlib_path is "./stdlib" (created by interpreter if missing)
        self.interpreter = TagScriptInterpreter(input_fn=self.request_input, output_fn=self._ide_output, stdlib_path=os.path.join(os.getcwd(), 'stdlib'))
        self._setup_keybindings()

        # start pumping the run_queue
        self.after(50, self._pump_queue)

    def _make_widgets(self):
        toolbar = tk.Frame(self)
        toolbar.pack(side='top', fill='x')
        btn_open = tk.Button(toolbar, text='Open', command=self.open_file)
        btn_open.pack(side='left')
        btn_save = tk.Button(toolbar, text='Save', command=self.save_file)
        btn_save.pack(side='left')
        btn_run = tk.Button(toolbar, text='Run', command=self.run_script)
        btn_run.pack(side='left')
        btn_stop = tk.Button(toolbar, text='Stop', command=self.stop_script)
        btn_stop.pack(side='left')

        paned = ttk.Panedwindow(self, orient='horizontal')
        paned.pack(fill='both', expand=True)

        editor_frame = tk.Frame(paned)
        paned.add(editor_frame, weight=3)
        self.editor = tk.Text(editor_frame, wrap='none', undo=True)
        self.editor.pack(fill='both', expand=True)

        right_frame = tk.Frame(paned, width=300)
        paned.add(right_frame, weight=1)

        console_label = tk.Label(right_frame, text='Console')
        console_label.pack()
        self.console = tk.Text(right_frame, height=15, bg='black', fg='white')
        self.console.pack(fill='both', expand=True)

        vars_label = tk.Label(right_frame, text='Variables')
        vars_label.pack()
        self.vars_box = tk.Text(right_frame, height=10)
        self.vars_box.pack(fill='both', expand=True)

    def _setup_keybindings(self):
        self.bind_all('<Control-s>', lambda e: self.save_file())
        self.bind_all('<Control-o>', lambda e: self.open_file())
        self.bind_all('<Control-r>', lambda e: self.run_script())

    # File operations (.tag-only by default)
    def open_file(self):
        path = filedialog.askopenfilename(filetypes=[('TagScript', '*.tag'), ('All', '*.*')])
        if not path:
            return
        with open(path, 'r', encoding='utf-8') as f:
            src = f.read()
        self.editor.delete('1.0', 'end')
        self.editor.insert('1.0', src)
        self.current_file = path
        self.title(f'TagScript IDE - {os.path.basename(path)}')

    def save_file(self):
        path = self.current_file or filedialog.asksaveasfilename(defaultextension='.tag', filetypes=[('TagScript', '*.tag'), ('All', '*.*')])
        if not path:
            return
        if not path.lower().endswith('.tag'):
            path = path + '.tag'
        with open(path, 'w', encoding='utf-8') as f:
            f.write(self.editor.get('1.0', 'end'))
        self.current_file = path
        self.title(f'TagScript IDE - {os.path.basename(path)}')

    # interpreter output adapter
    def _ide_output(self, text):
        self.run_queue.put(('out', str(text)))

    # Request input from user: called from interpreter worker thread
    def request_input(self, prompt=None):
        resp_q = queue.Queue(maxsize=1)
        self.run_queue.put(('input_request', (prompt or '', resp_q)))
        try:
            result = resp_q.get()  # block until GUI puts a response
            return result
        except Exception:
            return None

    def _update_vars_view(self):
        self.vars_box.delete('1.0', 'end')
        try:
            items = list(self.interpreter.env.items())
            for k, v in items:
                self.vars_box.insert('end', f"{k} = {repr(v)}\n")
        except Exception:
            pass

    def run_script(self):
        if self.run_thread and self.run_thread.is_alive():
            messagebox.showinfo('TagScript IDE', 'Script already running')
            return
        src = self.editor.get('1.0', 'end')
        self.console.delete('1.0', 'end')
        self.interpreter.reset()

        def worker():
            try:
                root = self.interpreter.parse(src)
            except Exception as e:
                self.run_queue.put(('err', f'Parse error: {e}'))
                self.run_queue.put(('vars', None))
                return
            try:
                self.interpreter.run(root)
                self.run_queue.put(('done', 'Execution finished'))
            except Exception as e:
                self.run_queue.put(('err', f'Runtime error: {e}'))
            finally:
                self.run_queue.put(('vars', None))

        self.run_thread = threading.Thread(target=worker, daemon=True)
        self.run_thread.start()

    def stop_script(self):
        if self.run_thread and self.run_thread.is_alive():
            self.interpreter.stop_requested = True
            self.run_queue.put(('out', 'Stop requested'))
        else:
            self.run_queue.put(('out', 'No running script'))

    def _pump_queue(self):
        try:
            while True:
                typ, payload = self.run_queue.get_nowait()
                if typ == 'out':
                    self.console.insert('end', str(payload) + '\n')
                    self.console.see('end')
                elif typ == 'err':
                    self.console.insert('end', '[ERROR] ' + str(payload) + '\n')
                    self.console.see('end')
                elif typ == 'done':
                    self.console.insert('end', str(payload) + '\n')
                elif typ == 'vars':
                    self._update_vars_view()
                elif typ == 'input_request':
                    prompt, resp_q = payload
                    try:
                        answer = simpledialog.askstring('Input requested', prompt or 'Input:')
                    except Exception:
                        answer = None
                    try:
                        resp_q.put(answer, timeout=1)
                    except Exception:
                        pass
        except queue.Empty:
            pass
        self.after(50, self._pump_queue)

    def _on_close(self):
        if messagebox.askokcancel('Quit', 'Exit TagScript IDE?'):
            if self.run_thread and self.run_thread.is_alive():
                self.interpreter.stop_requested = True
                time.sleep(0.05)
            self.destroy()

# -----------------------------
# Entry point
# -----------------------------
def main():
    app = TagScriptIDE()
    sample = '''<page>
    <start>
        <write>Welcome to TagScript!</write>
        <letssay name="name" value="'World'"/>
        <write>Hello {{ name }}</write>

        <!-- example loop -->
        <letssay name="i" value="0"/>
        <aslong value="i < 3">
            <write>Loop {{ i }}</write>
            <isnow name="i" value="i + 1"/>
        </aslong>

        <!-- example bring (local .tag module) -->
        <!-- <bring module="mymodule" /> -->

        <!-- example bring_net (remote .tag module by name) -->
        <!-- <bring_net name="example" /> -->

        <!-- example bring_net (remote .tag module via full url) -->
        <!-- <bring_net url="https://raw.githubusercontent.com/TheServer-lab/tagscriptonlinelibs/main/example.tag" /> -->

    </start>
</page>
'''
    app.editor.insert('1.0', sample)
    app.mainloop()

if __name__ == '__main__':
    main()
