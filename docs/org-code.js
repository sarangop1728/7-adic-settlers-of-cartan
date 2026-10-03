/* org-code.js — chrome for Org-exported source blocks.
 *
 * Loaded from init.org via `org-html-head-extra` (not `org-html-head`: the
 * website's .org files each set their own #+HTML_HEAD, which replaces that
 * variable outright).  Companion CSS lives in §8b of org-css.css.
 *
 * For every <pre class="src src-LANG"> it:
 *   1. wraps the <pre> in a .org-code-wrap,
 *   2. tags the wrapper data-lang="Magma" so CSS can print a label,
 *   3. appends a copy-to-clipboard button.
 *
 * Both pieces go in the wrapper, never inside the <pre>: the <pre> is the
 * horizontal scroller, and anything inside it is part of its textContent and
 * would end up in the clipboard.  The label is a CSS pseudo-element for the
 * same reason.
 *
 * No dependencies, no build step.  Degrades to Org's own hover label if this
 * file fails to load.
 */
(function () {
  'use strict';

  /* Org derives the class from whatever follows #+begin_src verbatim, so the
     keys here are Org language names, not file extensions.  Anything missing
     falls back to the raw name with its first letter capitalized. */
  var PRETTY = {
    'm': 'Magma',
    'magma': 'Magma',
    'sage': 'Sage',
    'python': 'Python',
    'emacs-lisp': 'Emacs Lisp',
    'elisp': 'Emacs Lisp',
    'lisp': 'Lisp',
    'sh': 'Shell',
    'bash': 'Shell',
    'shell': 'Shell',
    'latex': 'LaTeX',
    'js': 'JavaScript',
    'C': 'C',
    'C++': 'C++',
    'sql': 'SQL',
    'R': 'R',
    'gap': 'GAP',
    'pari': 'PARI/GP',
    'jupyter-python': 'Python'
  };

  var LABEL = 'Copy';
  var DONE = 'Copied!';
  var FAILED = 'Press ⌘C';
  var RESET_MS = 1200;

  function prettyName(lang) {
    if (Object.prototype.hasOwnProperty.call(PRETTY, lang)) return PRETTY[lang];
    return lang.charAt(0).toUpperCase() + lang.slice(1);
  }

  /* The language is only recoverable from the class list: Org emits
     class="src src-LANG" and nothing else. */
  function languageOf(pre) {
    var classes = pre.classList;
    for (var i = 0; i < classes.length; i++) {
      if (classes[i].indexOf('src-') === 0 && classes[i].length > 4) {
        return classes[i].slice(4);
      }
    }
    return null;
  }

  /* navigator.clipboard needs a secure context.  Exported notes are routinely
     opened straight off disk, and on file:// the API is usually absent — hence
     the execCommand path, which still works there.  Returns a promise so both
     branches look the same to the caller. */
  function legacyCopy(text) {
    var ta = document.createElement('textarea');
    ta.value = text;
    ta.setAttribute('readonly', '');
    /* Off-screen rather than display:none — a hidden element cannot be
       selected, and scrolling must not jump. */
    ta.style.position = 'fixed';
    ta.style.top = '-1000px';
    ta.style.opacity = '0';
    document.body.appendChild(ta);

    var selection = document.getSelection();
    var previous = selection.rangeCount > 0 ? selection.getRangeAt(0) : null;

    var ok = false;
    try {
      ta.select();
      ok = document.execCommand('copy');
    } catch (e) {
      ok = false;
    }

    document.body.removeChild(ta);
    if (previous) {
      selection.removeAllRanges();
      selection.addRange(previous);
    }
    return ok ? Promise.resolve() : Promise.reject(new Error('execCommand copy failed'));
  }

  function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) {
      return navigator.clipboard.writeText(text).catch(function () {
        return legacyCopy(text);
      });
    }
    return legacyCopy(text);
  }

  /* If neither copy path exists there is nothing to offer, and a button that
     does nothing is worse than no button. */
  function copyIsPossible() {
    return !!(navigator.clipboard && window.isSecureContext) ||
           (typeof document.execCommand === 'function' &&
            typeof document.queryCommandSupported === 'function' &&
            document.queryCommandSupported('copy'));
  }

  function makeButton(pre) {
    var btn = document.createElement('button');
    btn.type = 'button';
    btn.className = 'org-copy-btn';
    btn.textContent = LABEL;
    btn.setAttribute('aria-label', 'Copy code to clipboard');
    /* Announce the outcome, so the confirmation is not mouse-only. */
    btn.setAttribute('aria-live', 'polite');

    var timer = null;

    btn.addEventListener('click', function () {
      copyText(pre.textContent).then(function () {
        btn.textContent = DONE;
        btn.classList.add('copied');
      }, function () {
        btn.textContent = FAILED;
      }).then(function () {
        if (timer) clearTimeout(timer);
        timer = setTimeout(function () {
          btn.textContent = LABEL;
          btn.classList.remove('copied');
          /* Deliberately no blur() here: a keyboard user who tabbed to this
             button should keep their place, and a focused button staying
             visible is correct, not a leak. */
        }, RESET_MS);
      });
    });

    return btn;
  }

  function decorate(pre) {
    if (pre.parentNode && pre.parentNode.classList.contains('org-code-wrap')) return;

    var wrap = document.createElement('div');
    wrap.className = 'org-code-wrap';

    var lang = languageOf(pre);
    if (lang) wrap.setAttribute('data-lang', prettyName(lang));

    pre.parentNode.insertBefore(wrap, pre);
    wrap.appendChild(pre);

    if (copyIsPossible()) wrap.appendChild(makeButton(pre));
  }

  function init() {
    var blocks = document.querySelectorAll('pre.src');
    for (var i = 0; i < blocks.length; i++) decorate(blocks[i]);
  }

  /* The tag is loaded with `defer`, but guard anyway in case it is ever
     inlined into <head> without it. */
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
