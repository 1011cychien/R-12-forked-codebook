"""Convert content.yaml to content.tex + content.html"""

import argparse
import hashlib
import subprocess
from typing import List, Dict, Any, IO
from os import path
import yaml
from git import Repo


def md5hex(raw_s: str) -> str:
    """compute md5 hex string"""
    md5 = hashlib.md5()
    md5.update(raw_s.encode("utf8"))
    return md5.hexdigest()


def strip_whitespaces(raw_s: str) -> str:
    """works as `tr -d '[:space:]'`"""
    whitespaces = [" ", "\n", "\r", "\t", "\v"]
    return "".join(char for char in raw_s if char not in whitespaces)


def escape_latex(raw_s: str) -> str:
    """escape latex special characters"""
    escape_list = {
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
    }
    return "".join(escape_list.get(char, char) for char in raw_s)


def gen_tex(sections: List[Dict[str, Any]], out: IO) -> None:
    """generate content.tex"""
    for section in sections:
        title = escape_latex(section["name"])
        prefix = section["prefix"]
        out.write("\\SectionTitle{%s}\n" % title)
        out.write("\\renewcommand\\Prefix{%s}\n" % prefix)
        for content in section["content"]:
            base, ext = path.splitext(content["path"])
            if ext == ".cpp":
                preprocessed = subprocess.check_output(
                    [
                        "cpp",
                        "-dD",
                        "-P",
                        "-fpreprocessed",
                        path.join(prefix, content["path"]),
                    ]
                ).decode("utf8")
                stripped = strip_whitespaces(preprocessed)
                cpp_hash = md5hex(stripped)[:6]
                out.write(
                    "\\IncludeCode[C++][%s]{%s}{%s}\n"
                    % (
                        " {\\small [%s]}" % cpp_hash,
                        escape_latex(content["name"]),
                        content["path"],
                    )
                )
            elif ext == ".tex":
                out.write(
                    "\\IncludeTex{%s}{%s}\n"
                    % (escape_latex(content["name"]), content["path"])
                )
            elif base == "vimrc":
                out.write(
                    "\\IncludeCode[vim]{%s}{%s}\n"
                    % (escape_latex(content["name"]), content["path"])
                )
            else:
                raise NotImplementedError(f"unsupported extension name: {ext}")


def gen_html(sections: List[Dict[str, Any]], out: IO) -> None:
    """generate content.html"""
    out.write(
        """<!doctype html>
<html>
<head>
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta charset="utf8">
<title>ckiseki codebook</title>
<style>
html, body, div, span, applet, object, iframe,
h1, h2, h3, h4, h5, h6, p, blockquote, pre,
a, abbr, acronym, address, big, cite, code,
del, dfn, em, img, ins, kbd, q, s, samp,
small, strike, strong, sub, sup, tt, var,
b, u, i, center,
dl, dt, dd, ol, ul, li,
fieldset, form, label, legend,
table, caption, tbody, tfoot, thead, tr, th, td,
article, aside, canvas, details, embed,
figure, figcaption, footer, header, hgroup,
menu, nav, output, ruby, section, summary,
time, mark, audio, video {
  margin: 0;
  padding: 0;
  border: 0;
  font-size: 100%;
  font: inherit;
  vertical-align: baseline;
}
/* HTML5 display-role reset for older browsers */
article, aside, details, figcaption, figure,
footer, header, hgroup, menu, nav, section {
  display: block;
}
body {
  line-height: 1;
}
ol, ul {
  list-style: none;
}
blockquote, q {
  quotes: none;
}
blockquote:before, blockquote:after,
q:before, q:after {
  content: '';
  content: none;
}
table {
  border-collapse: collapse;
  border-spacing: 0;
}
body {
  font-family: sans-serif;
}
h1 {
  font-size: 1.5rem;
  font-weight: 600;
}
h2 {
  font-size: 1.2rem;
  font-weight: 600;
  margin-top: 10px;
}
.container {
  padding: 80px 10%;
}
li {
  margin-top: 5px;
}
</style>
</head>
<body>
<div class="container">
  <h1>ckiseki</h1>
  <hr/>
"""
    )
    repo = Repo("..")
    for section in sections:
        prefix = section["prefix"]
        out.write(f"<h2>{section['name']}</h2><ul>\n")
        for content in section["content"]:
            out.write("<li>")
            file_path = path.join(prefix, content["path"])
            real_path = path.realpath(file_path)
            commit_hash = str(
                list(repo.iter_commits(max_count=1, paths=real_path))[0]
            )
            if content["verified"] is None:
                out.write(b"\xe2\x9d\x8c".decode("utf8"))
            elif (
                content["verified"] != commit_hash[: len(content["verified"])]
            ):
                out.write(b"\xe2\x9a\xa0\xef\xb8\x8f".decode("utf8"))
            else:
                out.write(b"\xe2\x9c\x85".decode("utf8"))
            out.write(f" {content['name']}</li>")
        out.write("</ul>")
    out.write("</div></body></html>")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate Contents")
    parser.add_argument(
        "content_yaml", type=argparse.FileType("r", encoding="utf8")
    )
    parser.add_argument("--tex", type=argparse.FileType("w", encoding="utf8"))
    parser.add_argument("--html", type=argparse.FileType("w", encoding="utf8"))
    args = parser.parse_args()
    sections_list = yaml.safe_load(args.content_yaml)
    if args.tex:
        gen_tex(sections_list, args.tex)
    if args.html:
        gen_html(sections_list, args.html)
