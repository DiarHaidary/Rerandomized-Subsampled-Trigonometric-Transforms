(() => {
  "use strict";
  // SVG and MathML carry their own presentation and geometry attributes, and a
  // `dialog` draws itself over the document without needing any. The
  // literate-code genre emits none of the three, so their subtrees go rather
  // than being filtered attribute by attribute. Foreign tag names keep their
  // own case, so match on the folded one.
  const blocked = new Set([
    "APPLET", "BASE", "DIALOG", "EMBED", "FORM", "FRAME", "FRAMESET", "IFRAME",
    "MATH", "META", "OBJECT", "SCRIPT", "SVG"
  ]);
  const activeAttributes = new Set([
    "action", "formaction", "ping", "srcdoc"
  ]);
  // Presentation and visibility without a stylesheet: the legacy colour
  // attributes, the sizing pair, the top-layer controls, and the one that
  // hides honest content so that dishonest content can stand in for it. Verso
  // emits none of them here, `<meta name="viewport">` being a meta element and
  // dropped whole.
  const presentationAttributes = new Set([
    "alink", "background", "bgcolor", "height", "hidden", "link", "popover",
    "popovertarget", "popovertargetaction", "text", "vlink", "width"
  ]);
  // Verso's literate-code output needs one inline declaration, the indent
  // custom property its stylesheet reads, whose value is the source column the
  // documentation starts at. Any other one is enough to reposition or repaint
  // a page served with `style-src 'unsafe-inline'`. The whitespace is spelled
  // out because `\s` does not mean the same thing here as it does in Python.
  const allowedStyle = /^[ \t\r\n\f]*--indent:[ \t\r\n\f]*[0-9]{1,2}[ \t\r\n\f]*;?[ \t\r\n\f]*$/;

  function safeUrl(value, attribute) {
    const trimmed = value.trim();
    if (!trimmed || trimmed.startsWith("#") || trimmed.startsWith("./")) return true;
    if (trimmed.startsWith("../")) {
      if (trimmed.includes("\\")) return false;
      try {
        return !trimmed.slice(3).split("/")
          .map((part) => decodeURIComponent(part).toLowerCase())
          .some((part) => part === "." || part === "..");
      } catch (_) {
        return false;
      }
    }
    return attribute === "src" && /^data:image\/(?:gif|jpeg|png|webp);/i.test(trimmed);
  }

  function sanitize(root) {
    for (const element of Array.from(root.querySelectorAll("*"))) {
      if (blocked.has(element.tagName.toUpperCase())) {
        element.remove();
        continue;
      }
      for (const attribute of Array.from(element.attributes)) {
        const name = attribute.name.toLowerCase();
        if (name.startsWith("on") || activeAttributes.has(name)
            || presentationAttributes.has(name)) {
          element.removeAttribute(attribute.name);
        } else if (name === "open" && element.tagName.toUpperCase() !== "DETAILS") {
          // Verso emits `open` only on `<details>`: the module tree's, and the
          // trace ones it leaves expanded.
          element.removeAttribute(attribute.name);
        } else if (name === "src" && !safeUrl(attribute.value, name)) {
          element.removeAttribute(attribute.name);
        } else if (name === "href" && !safeUrl(attribute.value, name)) {
          element.removeAttribute(attribute.name);
        } else if (name === "style" && !allowedStyle.test(attribute.value)) {
          element.removeAttribute(attribute.name);
        } else if (name === "target") {
          element.removeAttribute(attribute.name);
        }
      }
    }
  }

  if (typeof marked !== "undefined" && typeof marked.parse === "function") {
    const parse = marked.parse.bind(marked);
    marked.parse = (...args) => {
      const template = document.createElement("template");
      template.innerHTML = parse(...args);
      sanitize(template.content);
      return template.innerHTML;
    };
  }
  window.palomarSanitize = sanitize;
  document.addEventListener("DOMContentLoaded", () => sanitize(document), {once: true});
})();
