/* book.js — navigation for the web book.
 *
 *  1. The Contents button opens and closes the sidebar on narrow screens.
 *  2. While reading, the section on screen is marked in the sidebar.
 *  3. A link into a folded proof opens the fold around it.
 *
 * Every page works without this file: the sidebar is plain links, on wide
 * screens it is always visible, and the proofs fold by themselves.
 */
(function () {
  'use strict';

  var body = document.body;
  var nav = document.getElementById('ec-sidebar');
  var button = document.querySelector('.ec-menu');

  /* Proofs are folded, and the glossary links straight at the terms defined
   * inside them, so open the fold around whatever the URL names: no browser
   * does that for a link, and only Chrome does it for find-in-page. */
  function reveal() {
    var id = location.hash ? decodeURIComponent(location.hash.slice(1)) : '';
    var target = id && document.getElementById(id);
    var folded = target && target.closest('details:not([open])');
    if (!folded) return;
    folded.open = true;
    target.scrollIntoView();
  }
  window.addEventListener('hashchange', reveal);
  reveal();
  /* Equation anchors are MathJax's, and do not exist yet. */
  if (window.MathJax && MathJax.startup) MathJax.startup.promise.then(reveal);

  if (!nav) return;

  function setOpen(open) {
    body.classList.toggle('ec-nav-open', open);
    if (button) button.setAttribute('aria-expanded', open ? 'true' : 'false');
  }

  if (button) {
    button.addEventListener('click', function () {
      setOpen(!body.classList.contains('ec-nav-open'));
    });
    nav.addEventListener('click', function (event) {
      if (event.target.closest('a')) setOpen(false);
    });
    document.addEventListener('keydown', function (event) {
      if (event.key === 'Escape' && body.classList.contains('ec-nav-open')) {
        setOpen(false);
        button.focus();
      }
    });
  }

  /* Section numbers carry ids like "s1.2"; the sidebar links to them. */
  var links = nav.querySelectorAll('.ec-toc-sections a[href^="#"]');
  if (!links.length || !('IntersectionObserver' in window)) return;

  var byTarget = new Map();
  links.forEach(function (link) {
    var target = document.getElementById(decodeURIComponent(link.hash.slice(1)));
    if (target) byTarget.set(target.closest('h2, h3, h4') || target, link);
  });

  var visible = new Set();
  function mark() {
    var first = null;
    byTarget.forEach(function (link, heading) {
      if (visible.has(heading) && (!first || heading.compareDocumentPosition(first) & Node.DOCUMENT_POSITION_FOLLOWING)) {
        first = heading;
      }
    });
    if (!first) return;
    links.forEach(function (link) { link.classList.remove('is-active'); });
    byTarget.get(first).classList.add('is-active');
  }

  var observer = new IntersectionObserver(function (entries) {
    entries.forEach(function (entry) {
      if (entry.isIntersecting) visible.add(entry.target);
      else visible.delete(entry.target);
    });
    mark();
  }, { rootMargin: '0px 0px -65% 0px' });

  byTarget.forEach(function (_link, heading) { observer.observe(heading); });
})();
